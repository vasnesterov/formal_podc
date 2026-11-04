import Papers.PODC2014.EventualLinParadox.ImplModel
import Papers.PODC2014.EventualLinParadox.Locality

/-!
# Proposition 16: eventually linearizable consensus from eventually linearizable registers

Guerraoui, Ruppert. *A Paradox of Eventual Linearizability in Shared Memory.* PODC 2014.

**Proposition 16.** A consensus object has a wait-free, eventually linearizable implementation
from eventually linearizable registers (`prop16`).

Model: processes `Fin N`, registers `Proposal[0..N-1]` (`regT D`: values `Option D`, initially
`⊥ = none`; `write v` with `v : D` returns `none`), semantics `elSys` of `ImplModel`: base
accesses are split into invocation and response, the adversary chooses the responses, and an
execution is admissible (`ELAdm`) iff every register's history is eventually linearizable
(weakly consistent and `tₓ`-linearizable for some `tₓ`). The algorithm (`consImpl`):
`Propose(v)` by `pᵢ`: read `Proposal[i]`; if `⊥`, write `v`; read `Proposal[0..N-1]` and return
the leftmost non-`⊥` value.

Proof structure:
* `Prop16.el_step`: the possible steps of `elSys` (generic in the implementation).
* `Prop16.PInv`/`Prop16.inv_all`: an invariant of admissible executions, by local state. It uses
  two consequences of the weak consistency of the registers (`adm_R1`: a read returning `w` is
  preceded by a write of `w`; `adm_R2`: a read by `pᵢ` of `Proposal[i]` after a completed write
  of `pᵢ` to it returns non-`⊥`). Consequences: writes to `Proposal[x]` are by `p_x`, during its
  first operation (`inv_write`), at most once (`write_unique`); a completed operation returns the
  leftmost non-`⊥` value of its scan (`inv_res`; the fallback is never used).
* `cons_weaklyConsistent`: Definition 1 for the consensus history.
* `cons_exists_tLin`: some `t`-linearization. We argue per register (no Lemma 7): each register
  is written at most once, so from some time on all its reads return a fixed value
  (`reg_stable`); operations invoked afterwards return the same value `w₀`, proposed by the
  operation `op₀` that wrote it; `op₀` followed by all other completed operations in the order of
  their responses, all returning `w₀`, is a `t`-linearization for large `t`.
* `cons_waitFree`: a progress measure (`meas`).
-/

namespace Podc.EventualLinParadox

/-! ### The types and the algorithm -/

/-- The **consensus** type over values `D`: the state is the decided value (`none` initially);
`propose v` decides `v` if nothing is decided yet and returns the decided value. -/
def consT (D : Type) : ObjType (Option D) D D where
  init := {none}
  δ q v r q' := (q = none ∧ r = v ∧ q' = some v) ∨ (q = some r ∧ q' = q)

/-- Read/write register operations (values of `D`; the initial value `⊥ = none` is never
written). -/
inductive RWOp (D : Type) where
  | read
  | write (v : D)

/-- A read/write **register** holding `Option D`, initially `⊥ = none`; `write` returns the
acknowledgement `none`. -/
def regT (D : Type) : ObjType (Option D) (RWOp D) (Option D) where
  init := {none}
  δ q o r q' := match o with
    | .read => r = q ∧ q' = q
    | .write v => r = none ∧ q' = some v

/-- Local states of the consensus algorithm: idle; about to read `Proposal[i]` (`chk v`);
about to write `v` to `Proposal[i]` (`wr v`); scanning `Proposal[j]` with the leftmost
non-`⊥` value `best` seen so far (`scan v j best`). -/
inductive CLoc (D : Type) where
  | idle
  | chk (v : D)
  | wr (v : D)
  | scan (v : D) (j : ℕ) (best : Option D)

/-- Keep the leftmost non-`⊥` value. -/
def consPick {D : Type} : Option D → Option D → Option D
  | some w, _ => some w
  | none, r => r

/-- The algorithm of Proposition 16 for processes `Fin N` and registers `Proposal[0..N-1]`:
`Propose(v)` by `pᵢ`: if `Proposal[i] = ⊥` then `Proposal[i] := v`; read `Proposal[0..N-1]`
and return the leftmost non-`⊥` value (the fallback `v` is never used). -/
def consImpl (N : ℕ) (D : Type) :
    Impl (Fin N) D D (Fin N) (RWOp D) (Option D) (CLoc D) where
  locInit _ := .idle
  invoke _ _ v := .chk v
  act p l := match l with
    | .idle => .loc .idle
    | .chk v => .call p .read (fun r => match r with
        | none => .wr v
        | some _ => .scan v 0 none)
    | .wr v => .call p (.write v) (fun _ => .scan v 0 none)
    | .scan v j best =>
      if h : j < N then .call ⟨j, h⟩ .read (fun r => .scan v (j + 1) (consPick best r))
      else .ret (best.getD v) .idle

/-! Auxiliary definitions and lemmas live in the namespace `Prop16`. -/

namespace Prop16

/-! ### One step of the semantics -/

section StepCases

variable {P HOp HRes X BOp BRes L : Type} [DecidableEq P] (I : Impl P HOp HRes X BOp BRes L)
  (lab : ℕ → Option (ELab P HOp BRes)) (n : ℕ)

/-- The possible steps of `elSys`. -/
lemma el_step :
    let c := (elSys I).cfg lab n
    let c' := (elSys I).cfg lab (n + 1)
    let e := (elSys I).hist lab n
    let be := (elSys I).bhist lab n
    (c' = c ∧ e = none ∧ be = none ∧ ∀ l, lab n = some l → elStep I n c l = none) ∨
    (∃ p op, lab n = some (.inv p op) ∧ c.pend p = none ∧
      c' = ⟨Function.update c.loc p (I.invoke p (c.loc p) op), Function.update c.pend p (some n),
        c.bpend⟩ ∧ e = some (.inv p () op) ∧ be = none) ∨
    (∃ p a x o k, lab n = some (.step p) ∧ c.pend p = some a ∧ c.bpend p = none ∧
      I.act p (c.loc p) = .call x o k ∧ c' = ⟨c.loc, c.pend, Function.update c.bpend p (some n)⟩ ∧
      e = none ∧ be = some (.inv p x o)) ∨
    (∃ p a l', lab n = some (.step p) ∧ c.pend p = some a ∧ c.bpend p = none ∧
      I.act p (c.loc p) = .loc l' ∧ c' = ⟨Function.update c.loc p l', c.pend, c.bpend⟩ ∧
      e = none ∧ be = none) ∨
    (∃ p a r l', lab n = some (.step p) ∧ c.pend p = some a ∧ c.bpend p = none ∧
      I.act p (c.loc p) = .ret r l' ∧
      c' = ⟨Function.update c.loc p l', Function.update c.pend p none, c.bpend⟩ ∧
      e = some (.res a r) ∧ be = none) ∨
    (∃ p r b x o k, lab n = some (.bres p r) ∧ c.bpend p = some b ∧ I.act p (c.loc p) = .call x o k ∧
      c' = ⟨Function.update c.loc p (k r), c.pend, Function.update c.bpend p none⟩ ∧
      e = none ∧ be = some (.res b r)) := by
  simp only [elSys_cfg_succ, elSys_hist, elSys_bhist]
  generalize (elSys I).cfg lab n = c
  rcases hl : lab n with _ | l
  · left; simp
  · cases l with
    | inv p op =>
      simp only [Option.bind_some, elStep]
      split_ifs with h
      · right; left; exact ⟨p, op, rfl, h, rfl, rfl, rfl⟩
      · left; simp [h]
    | step p =>
      simp only [Option.bind_some, elStep]
      rcases hp : c.pend p with _ | a
      · left; simp [hp]
      rcases hb : c.bpend p with _ | b
      swap; · left; simp [hp, hb]
      cases hact : I.act p (c.loc p) with
      | call x o k => right; right; left; exact ⟨p, a, x, o, k, rfl, hp, hb, hact, rfl, rfl, rfl⟩
      | loc l => right; right; right; left; exact ⟨p, a, l, rfl, hp, hb, hact, rfl, rfl, rfl⟩
      | ret r l => right; right; right; right; left; exact ⟨p, a, r, l, rfl, hp, hb, hact, rfl, rfl, rfl⟩
    | bres p r =>
      simp only [Option.bind_some, elStep]
      rcases hb : c.bpend p with _ | b
      · left; simp [hb]
      · cases hact : I.act p (c.loc p) with
        | call x o k =>
          right; right; right; right; right; exact ⟨p, r, b, x, o, k, rfl, hb, hact, rfl, rfl, rfl⟩
        | loc l => left; simp [hb, hact]
        | ret r' l => left; simp [hb, hact]

end StepCases

/-! ### Legal register histories -/

section Reg

variable {P X D : Type} {H : History P X (RWOp D) (Option D)}

lemma reg_q1 {S : SeqHist (Option D)} {x : X} {q : ℕ → Option D}
    (hq : ∀ k, SeqStep (regT D) H x (S k) (q k) (q (k + 1))) (hq0 : q 0 = none) :
    ∀ k, q k = none ∨ ∃ k1 < k, ∃ b1 r1 p1 w, S k1 = some (b1, r1) ∧
      H b1 = some (.inv p1 x (.write w)) ∧ q k = some w := by
  intro k
  induction k with
  | zero => exact Or.inl hq0
  | succ k ih =>
    have hs := hq k
    have keep : q (k + 1) = q k → q (k + 1) = none ∨ ∃ k1 < k + 1, ∃ b1 r1 p1 w,
        S k1 = some (b1, r1) ∧ H b1 = some (.inv p1 x (.write w)) ∧ q (k + 1) = some w := by
      intro he
      rw [he]
      rcases ih with h | ⟨k1, hk1, b1, r1, p1, w, h1, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨k1, by omega, b1, r1, p1, w, h1, h2, h3⟩
    cases hS : S k with
    | none => rw [hS] at hs; exact keep hs
    | some e =>
      obtain ⟨b, r⟩ := e
      rw [hS] at hs
      rcases hs with ⟨p, op, hb, hδ⟩ | ⟨-, he⟩
      · cases op with
        | read => exact keep hδ.2
        | write w => exact Or.inr ⟨k, by omega, b, r, p, w, hS, hb, hδ.2⟩
      · exact keep he

lemma reg_some_of_write {S : SeqHist (Option D)} {x : X} {q : ℕ → Option D}
    (hq : ∀ k, SeqStep (regT D) H x (S k) (q k) (q (k + 1))) {k1 b1 : ℕ} {r1 : Option D}
    {p1 : P} {w : D} (h1 : S k1 = some (b1, r1)) (h2 : H b1 = some (.inv p1 x (.write w))) :
    ∀ k, k1 < k → q k ≠ none := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · have ihk := ih hk
      have hs := hq k
      cases hS : S k with
      | none => rw [hS] at hs; rw [hs]; exact ihk
      | some e =>
        obtain ⟨b, r⟩ := e
        rw [hS] at hs
        rcases hs with ⟨p, op, hb, hδ⟩ | ⟨-, he⟩
        · cases op with
          | read => rw [hδ.2]; exact ihk
          | write w' => rw [hδ.2]; simp
        · rw [he]; exact ihk
    · have hs := hq k1
      rw [h1] at hs
      rcases hs with ⟨p, op, hb, hδ⟩ | ⟨hno, -⟩
      · rw [h2] at hb
        simp only [Option.some.injEq, Ev.inv.injEq] at hb
        obtain ⟨-, -, rfl⟩ := hb
        rw [hδ.2]; simp
      · exact absurd ⟨p1, _, h2⟩ hno

lemma reg_read_eq {S : SeqHist (Option D)} {x : X} {q : ℕ → Option D}
    (hq : ∀ k, SeqStep (regT D) H x (S k) (q k) (q (k + 1))) {k b : ℕ} {r : Option D} {p : P}
    (hk : S k = some (b, r)) (hb : H b = some (.inv p x .read)) : r = q k := by
  have hs := hq k
  rw [hk] at hs
  rcases hs with ⟨p', op, hb', hδ⟩ | ⟨hno, -⟩
  · rw [hb] at hb'
    simp only [Option.some.injEq, Ev.inv.injEq] at hb'
    obtain ⟨-, -, rfl⟩ := hb'
    exact hδ.1
  · exact absurd ⟨p, _, hb⟩ hno

/-- A read returning `some w` is preceded by a write of `w` (weak consistency). -/
lemma reg_wc_read_some (hWC : WeaklyConsistent (fun _ => regT D) H) {b b' : ℕ} {p : P} {x : X}
    {w : D} (hb : H b = some (.inv p x .read)) (hb' : H b' = some (.res b (some w))) :
    ∃ bw < b', ∃ q', H bw = some (.inv q' x (.write w)) := by
  obtain ⟨S, -, hleg, hlt, -, k, hk, -⟩ := hWC b b' (some w) hb'
  obtain ⟨q, hq0, hq⟩ := hleg.2 x
  have hr := reg_read_eq hq hk hb
  rcases reg_q1 hq hq0 k with h | ⟨k1, -, b1, r1, p1, w', h1, h2, h3⟩
  · rw [h] at hr; cases hr
  · rw [h3] at hr
    cases hr
    exact ⟨b1, hlt b1 ⟨k1, r1, h1⟩, p1, h2⟩

/-- A read by a process that has a completed write to the same register returns a non-`⊥`
value (weak consistency). -/
lemma reg_wc_read_ne_none (hWC : WeaklyConsistent (fun _ => regT D) H) {b b' bw bw' : ℕ}
    {p : P} {x : X} {r r' : Option D} {v : D} (hb : H b = some (.inv p x .read))
    (hb' : H b' = some (.res b r)) (hbw : H bw = some (.inv p x (.write v)))
    (hbw' : H bw' = some (.res bw r')) (hlt : bw' < b) : r ≠ none := by
  obtain ⟨S, hnd, hleg, -, hproc, k, hk, hlast⟩ := hWC b b' r hb'
  obtain ⟨q, hq0, hq⟩ := hleg.2 x
  obtain ⟨k1, r1, hk1⟩ := hproc bw ⟨p, x, x, _, _, hbw, hb⟩ ⟨bw', r', hbw', hlt, p, x, _, hb⟩
  have hk1k : k1 < k := by
    rcases lt_trichotomy k1 k with h | rfl | h
    · exact h
    · rw [hk] at hk1
      simp only [Option.some.injEq, Prod.mk.injEq] at hk1
      obtain ⟨rfl, -⟩ := hk1
      rw [hb] at hbw; simp at hbw
    · rw [hlast k1 h] at hk1; cases hk1
  rw [reg_read_eq hq hk hb]
  exact reg_some_of_write hq hk1 hbw k hk1k

lemma exists_slot_resp_bound (hWF : WellFormed H) (S : SeqHist (Option D)) (K : ℕ) :
    ∃ M, ∀ k < K, ∀ b r' b' r, S k = some (b, r') → H b' = some (.res b r) → b' < M := by
  induction K with
  | zero => exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ K ih =>
    obtain ⟨M, hM⟩ := ih
    by_cases h : ∃ b r' b' r, S K = some (b, r') ∧ H b' = some (.res b r)
    · obtain ⟨b, r', b', r, h1, h2⟩ := h
      refine ⟨max M (b' + 1), fun k hk c rc c' rr hc hc' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · have := hM k hk c rc c' rr hc hc'; omega
      · rw [h1] at hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨hbc, -⟩ := hc
        subst hbc
        have := hWF.res_unique _ _ _ _ _ h2 hc'
        omega
    · refine ⟨M, fun k hk c rc c' rr hc hc' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact hM k hk c rc c' rr hc hc'
      · exact absurd ⟨c, rc, c', rr, hc, hc'⟩ h

/-- A `t`-linearizable register history with at most one write: from some time on, all reads
return the same value `fin` (the written value if the write is linearized, `⊥` otherwise). -/
lemma reg_stable (hWF : WellFormed H) {x : X} {t : ℕ} {S : SeqHist (Option D)}
    (hS : IsTLin (fun _ => regT D) H t S)
    (hW1 : ∀ b1 b2 p1 p2 w1 w2, H b1 = some (.inv p1 x (.write w1)) →
      H b2 = some (.inv p2 x (.write w2)) → b1 = b2) :
    ∃ T fin, (∀ b b' p r, H b = some (.inv p x .read) → H b' = some (.res b r) → T ≤ b' →
      r = fin) ∧ (∀ w, fin = some w → ∃ bw p, H bw = some (.inv p x (.write w))) := by
  obtain ⟨q, hq0, hq⟩ := hS.legal.2 x
  by_cases hw : ∃ kw bw rw pw w, S kw = some (bw, rw) ∧ H bw = some (.inv pw x (.write w))
  · obtain ⟨kw, bw, rw, pw, w, hkw, hbw⟩ := hw
    obtain ⟨M, hM⟩ := exists_slot_resp_bound hWF S kw
    refine ⟨max t M, some w, fun b b' p r hb hb' hT => ?_,
      fun w' hw' => ⟨bw, pw, by cases hw'; exact hbw⟩⟩
    obtain ⟨k, hk⟩ := hS.resp b b' r hb' (by omega)
    rw [reg_read_eq hq hk hb]
    rcases lt_trichotomy k kw with hlt | rfl | hlt
    · have := hM k hlt b r b' r hk hb'; omega
    · rw [hkw] at hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      rw [hb] at hbw; simp at hbw
    · rcases reg_q1 hq hq0 k with h | ⟨k1, -, b1, r1, p1, w1, h1, h2, h3⟩
      · exact absurd h (reg_some_of_write hq hkw hbw k hlt)
      · rw [h3]
        have := hW1 b1 bw p1 pw w1 w h2 hbw
        subst this
        rw [hbw] at h2
        simp only [Option.some.injEq, Ev.inv.injEq, RWOp.write.injEq] at h2
        rw [h2.2.2]
  · push Not at hw
    refine ⟨t, none, fun b b' p r hb hb' hT => ?_, fun w h => by cases h⟩
    obtain ⟨k, hk⟩ := hS.resp b b' r hb' hT
    rw [reg_read_eq hq hk hb]
    rcases reg_q1 hq hq0 k with h | ⟨k1, -, b1, r1, p1, w1, h1, h2, h3⟩
    · exact h
    · exact absurd h2 (hw k1 b1 r1 p1 w1 h1)

end Reg

/-! ### Legal consensus histories -/

section ConsLegal

variable {P D : Type} {H : History P Unit D D}

/-- A sequential consensus history whose first entry is an operation proposing `w` and in which
every operation returns `w` is legal. -/
lemma legal_cons {S : SeqHist D} {a0 : ℕ} {p0 : P} {w : D}
    (h0 : S 0 = some (a0, w)) (ha0 : H a0 = some (.inv p0 () w))
    (hS : ∀ k b r, S k = some (b, r) → r = w ∧ Invoked H b) :
    Legal (fun _ => consT D) H S := by
  refine ⟨fun k b r hk => (hS k b r hk).2,
    fun x => ⟨fun k => if k = 0 then none else some w, by simp [consT], fun k => ?_⟩⟩
  cases hk : S k with
  | none =>
    have : k ≠ 0 := by rintro rfl; rw [h0] at hk; cases hk
    simp [SeqStep, this]
  | some e =>
    obtain ⟨b, r⟩ := e
    obtain ⟨rfl, p, y, op, hb⟩ := hS k b r hk
    left
    cases x; cases y
    by_cases hk0 : k = 0
    · subst hk0
      rw [h0] at hk
      simp only [Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, -⟩ := hk
      exact ⟨p0, r, ha0, by simp [consT]⟩
    · exact ⟨p, op, hb, by simp [consT, hk0]⟩

/-- The sequential history listing `l`, every operation returning `w`. -/
def listSeq (l : List ℕ) (w : D) : SeqHist D := fun k => (l[k]?).map (fun c => (c, w))

lemma listSeq_eq_some {l : List ℕ} {w : D} {k c : ℕ} {r : D} :
    listSeq l w k = some (c, r) ↔ l[k]? = some c ∧ r = w := by
  unfold listSeq
  cases h : l[k]? <;> simp [eq_comm]

lemma listSeq_mem {l : List ℕ} {w : D} {c : ℕ} : (listSeq l w).Mem c ↔ c ∈ l := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨k, r, hk⟩; exact ⟨k, (listSeq_eq_some.1 hk).1⟩
  · rintro ⟨k, hk⟩; exact ⟨k, w, listSeq_eq_some.2 ⟨hk, rfl⟩⟩

lemma listSeq_nodup {l : List ℕ} {w : D} (hl : l.Nodup) : (listSeq l w).Nodup := by
  intro k k' c r r' hk hk'
  have e1 := (listSeq_eq_some.1 hk).1
  have e2 := (listSeq_eq_some.1 hk').1
  have hlt : k < l.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at e1; cases e1
  exact hl.eq_of_getElem?_eq hlt (e1.trans e2.symm)

lemma listSeq_last {l : List ℕ} {w : D} {a : ℕ} :
    ∃ k, listSeq (l ++ [a]) w k = some (a, w) ∧ ∀ k', k < k' → listSeq (l ++ [a]) w k' = none := by
  refine ⟨l.length, by simp [listSeq], fun k' hk' => ?_⟩
  simp only [listSeq, Option.map_eq_none_iff]
  exact List.getElem?_eq_none (by simp; omega)

end ConsLegal

/-! ### Generic facts on histories -/

section Generic

variable {P X Op Res Q : Type} {H : History P X Op Res}

lemma exists_resp_bound_gen (hH : WellFormed H) (n : ℕ) :
    ∃ M, ∀ c < n, ∀ j r, H j = some (.res c r) → j < M := by
  induction n with
  | zero => exact ⟨0, fun c hc => absurd hc (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨M, hM⟩ := ih
    by_cases h : ∃ jn rn, H jn = some (.res n rn)
    · obtain ⟨jn, rn, hn⟩ := h
      refine ⟨max M (jn + 1), fun c hc j r hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · have := hM c hc j r hj; omega
      · have := hH.res_unique _ _ _ _ _ hj hn; omega
    · refine ⟨M, fun c hc j r hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · exact hM c hc j r hj
      · exact absurd ⟨j, r, hj⟩ h

/-- A history without responses at positions `≥ t` is `t`-linearizable (total types). -/
lemma tLinearizable_of_no_late {spec : X → ObjType Q Op Res} (hI : ∀ x, (spec x).init.Nonempty)
    (hT : ∀ x, (spec x).Total) (hH : WellFormed H) {t : ℕ}
    (h : ∀ j a r, H j = some (.res a r) → j < t) : TLinearizable spec H t := by
  obtain ⟨S, hS⟩ := tLinearizable_take_self hI hT hH t
  refine ⟨S, ⟨hS.nodup, hS.legal.congr fun k a r hk => ?_, fun a j r hj => ?_,
    fun a b j r hj htj => absurd (h j a r hj) (by omega),
    fun a j r hj htj => absurd (h j a r hj) (by omega)⟩⟩
  · exact (take_of_lt H ((invoked_take H).1 (hS.legal.1 k a r hk)).1).symm
  · exact hS.complete a j r ((take_eq_some H).2 ⟨h j a r hj, hj⟩)

end Generic

/-! ### The invariant of the algorithm -/

section Invariant

variable {N : ℕ} {D : Type}

/-- Process `p` has a completed write to its own register, responding before `t`. -/
def OwnW (BH : History (Fin N) (Fin N) (RWOp D) (Option D)) (p : Fin N) (t : ℕ) : Prop :=
  ∃ bw bw' v r, bw' < t ∧ BH bw = some (.inv p p (.write v)) ∧ BH bw' = some (.res bw r)

/-- Process `p` read `r` from register `x`, the read being invoked after `lo` and responding
before `hi`. -/
def ReadBy (BH : History (Fin N) (Fin N) (RWOp D) (Option D)) (p x : Fin N) (r : Option D)
    (lo hi : ℕ) : Prop :=
  ∃ b b', lo < b ∧ b' < hi ∧ BH b = some (.inv p x .read) ∧ BH b' = some (.res b r)

/-- Process `p` invoked an operation before `a`. -/
def EarlierOp (H : History (Fin N) Unit D D) (p : Fin N) (a : ℕ) : Prop :=
  ∃ a' < a, ∃ v, H a' = some (.inv p () v)

lemma OwnW.mono {BH : History (Fin N) (Fin N) (RWOp D) (Option D)} {p : Fin N} {t t' : ℕ}
    (h : OwnW BH p t) (ht : t ≤ t') : OwnW BH p t' :=
  let ⟨bw, bw', v, r, h1, h2, h3⟩ := h; ⟨bw, bw', v, r, by omega, h2, h3⟩

lemma ReadBy.mono {BH : History (Fin N) (Fin N) (RWOp D) (Option D)} {p x : Fin N} {r : Option D}
    {lo hi hi' : ℕ} (h : ReadBy BH p x r lo hi) (ht : hi ≤ hi') : ReadBy BH p x r lo hi' :=
  let ⟨b, b', h1, h2, h3, h4⟩ := h; ⟨b, b', h1, by omega, h3, h4⟩

/-- The per-process invariant, by local state. -/
def PInv (H : History (Fin N) Unit D D) (BH : History (Fin N) (Fin N) (RWOp D) (Option D))
    (n : ℕ) (p : Fin N) : CLoc D → Option ℕ → Option ℕ → Prop
  | .idle, pd, bp => pd = none ∧ bp = none ∧ (EarlierOp H p n → OwnW BH p n)
  | .chk v, pd, bp => ∃ a, pd = some a ∧ a < n ∧ H a = some (.inv p () v) ∧
      (EarlierOp H p a → OwnW BH p a) ∧
      (∀ b, a < b → b < n → ∀ w, BH b ≠ some (.inv p p (.write w))) ∧
      (∀ b, bp = some b → a < b ∧ b < n ∧ BH b = some (.inv p p .read))
  | .wr v, pd, bp => ∃ a, pd = some a ∧ a < n ∧ H a = some (.inv p () v) ∧ ¬ EarlierOp H p a ∧
      (∀ b, a < b → b < n → ∀ w, BH b = some (.inv p p (.write w)) → bp = some b) ∧
      (∀ b, bp = some b → a < b ∧ b < n ∧ BH b = some (.inv p p (.write v)))
  | .scan v j best, pd, bp => ∃ a, pd = some a ∧ a < n ∧ H a = some (.inv p () v) ∧
      OwnW BH p n ∧ (p.val < j → best ≠ none) ∧
      (best = none → ∀ y : Fin N, y.val < j → ReadBy BH p y none a n) ∧
      (∀ w, best = some w → ∃ x : Fin N, x.val < j ∧
        (∀ y : Fin N, y.val < x.val → ReadBy BH p y none a n) ∧ ReadBy BH p x (some w) a n) ∧
      (∀ b, bp = some b → a < b ∧ b < n ∧ OwnW BH p b ∧
        ∃ h : j < N, BH b = some (.inv p ⟨j, h⟩ .read))

lemma PInv.frame {H : History (Fin N) Unit D D} {BH : History (Fin N) (Fin N) (RWOp D) (Option D)}
    {n : ℕ} {p : Fin N} {l : CLoc D} {pd bp : Option ℕ} (h : PInv H BH n p l pd bp)
    (hH : ∀ v, H n ≠ some (.inv p () v)) (hB : ∀ x o, BH n ≠ some (.inv p x o)) :
    PInv H BH (n + 1) p l pd bp := by
  cases l with
  | idle =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, h2, fun ⟨a', ha', v, hv⟩ => (h3 ⟨a', ?_, v, hv⟩).mono (by omega)⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 ha' with h | rfl
    · exact h
    · exact absurd hv (hH v)
  | chk v =>
    obtain ⟨a, h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨a, h1, by omega, h3, h4, fun b hab hbn w => ?_, fun b hb => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hbn with hbn | rfl
      · exact h5 b hab hbn w
      · exact hB _ _
    · obtain ⟨h7, h8, h9⟩ := h6 b hb; exact ⟨h7, by omega, h9⟩
  | wr v =>
    obtain ⟨a, h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨a, h1, by omega, h3, h4, fun b hab hbn w hw => ?_, fun b hb => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hbn with hbn | rfl
      · exact h5 b hab hbn w hw
      · exact absurd hw (hB _ _)
    · obtain ⟨h7, h8, h9⟩ := h6 b hb; exact ⟨h7, by omega, h9⟩
  | scan v j best =>
    obtain ⟨a, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
    refine ⟨a, h1, by omega, h3, h4.mono (by omega), h5,
      fun hb y hy => (h6 hb y hy).mono (by omega), fun w hw => ?_, fun b hb => ?_⟩
    · obtain ⟨x, hx, hx1, hx2⟩ := h7 w hw
      exact ⟨x, hx, fun y hy => (hx1 y hy).mono (by omega), hx2.mono (by omega)⟩
    · obtain ⟨h9, h10, h11⟩ := h8 b hb; exact ⟨h9, by omega, h11⟩

/-- The invariant at time `n`. -/
def Inv (lab : ℕ → Option (ELab (Fin N) D (Option D))) (n : ℕ) : Prop :=
  ∀ p, PInv ((elSys (consImpl N D)).hist lab) ((elSys (consImpl N D)).bhist lab) n p
    (((elSys (consImpl N D)).cfg lab n).loc p) (((elSys (consImpl N D)).cfg lab n).pend p)
    (((elSys (consImpl N D)).cfg lab n).bpend p)

lemma inv_zero (lab : ℕ → Option (ELab (Fin N) D (Option D))) : Inv lab 0 :=
  fun _ => ⟨rfl, rfl, fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩

end Invariant

/-! ### Facts about executions derived from the invariant -/

section Exec

variable {N : ℕ} {D : Type} (lab : ℕ → Option (ELab (Fin N) D (Option D)))

local notation "𝒮" => elSys (consImpl N D)

/-- A base write to register `x` is by process `x`, during an operation proposing the written
value; that operation is the process's first one and the write is its only write so far. -/
lemma inv_write {b : ℕ} (hI : Inv lab b) {q x : Fin N} {w : D}
    (h : (𝒮).bhist lab b = some (.inv q x (.write w))) :
    x = q ∧ ∃ a, ((𝒮).cfg lab b).pend q = some a ∧ ((𝒮).cfg lab b).bpend q = none ∧ a < b ∧
      (𝒮).hist lab a = some (.inv q () w) ∧ ¬ EarlierOp ((𝒮).hist lab) q a ∧
      ∀ b2, a < b2 → b2 < b → ∀ w', (𝒮).bhist lab b2 ≠ some (.inv q q (.write w')) := by
  rcases el_step (consImpl N D) lab b with ⟨-, -, hbe, -⟩ | ⟨p, op, -, -, -, -, hbe⟩ |
    ⟨p, a, x', o, k, -, hpd, hbp, hact, -, -, hbe⟩ | ⟨p, a, l', -, -, -, -, -, -, hbe⟩ |
    ⟨p, a, r, l', -, -, -, -, -, -, hbe⟩ | ⟨p, r, b', x', o, k, -, -, -, -, -, hbe⟩
  all_goals rw [h] at hbe
  all_goals (try simp at hbe)
  obtain ⟨rfl, rfl, rfl⟩ := hbe
  have hp := hI q
  rcases hloc : ((𝒮).cfg lab b).loc q with _ | v | v | ⟨v, j, best⟩ <;>
    rw [hloc] at hp hact <;> simp [consImpl] at hact
  · obtain ⟨rfl, rfl, -⟩ := hact
    rw [hpd, hbp] at hp
    obtain ⟨a', ha', h1, h2, h3, h5, -⟩ := hp
    cases ha'
    refine ⟨rfl, _, hpd, hbp, h1, h2, h3, fun b2 hab hb2 w' hw' => ?_⟩
    have := h5 b2 hab hb2 w' hw'
    simp at this
  · split_ifs at hact; simp at hact

/-- The invariant is preserved, given the two consequences `hR1`, `hR2` of the weak
consistency of the registers. -/
lemma inv_succ (hWF : WellFormed ((𝒮).bhist lab))
    (hR1 : ∀ b b' (q x : Fin N) w, (𝒮).bhist lab b = some (.inv q x .read) →
      (𝒮).bhist lab b' = some (.res b (some w)) →
      ∃ bw < b', ∃ q', (𝒮).bhist lab bw = some (.inv q' x (.write w)))
    (hR2 : ∀ b b' (p : Fin N) r, (𝒮).bhist lab b = some (.inv p p .read) →
      (𝒮).bhist lab b' = some (.res b r) → OwnW ((𝒮).bhist lab) p b → r ≠ none)
    {n : ℕ} (hall : ∀ k ≤ n, Inv lab k) : Inv lab (n + 1) := by
  intro p
  have hp := hall n le_rfl p
  rcases el_step (consImpl N D) lab n with ⟨hc', he, hbe, -⟩ | ⟨q, op, -, hpd, hc', he, hbe⟩ |
    ⟨q, a, x, o, k, -, hpd, hbp, hact, hc', he, hbe⟩ | ⟨q, a, l', -, hpd, hbp, hact, hc', he, hbe⟩ |
    ⟨q, a, r, l', -, hpd, hbp, hact, hc', he, hbe⟩ | ⟨q, r, b, x, o, k, -, hbp, hact, hc', he, hbe⟩
  · rw [hc']; exact hp.frame (by simp [he]) (by simp [hbe])
  · -- invocation
    rw [hc']; dsimp only
    by_cases hpq : p = q
    · subst hpq
      simp only [Function.update_self]
      show PInv _ _ (n + 1) p (.chk op) (some n) _
      rcases hloc : ((𝒮).cfg lab n).loc p with _ | v | v | ⟨v, j, best⟩ <;> rw [hloc] at hp
      · obtain ⟨-, hbp, hE⟩ := hp
        exact ⟨n, rfl, by omega, he, hE, fun b hb1 hb2 => by omega,
          fun b hb => by rw [hbp] at hb; cases hb⟩
      all_goals (obtain ⟨a, ha, -⟩ := hp; rw [hpd] at ha; cases ha)
    · simp only [Function.update_of_ne hpq]
      exact hp.frame (by simp [he, Ne.symm hpq]) (by simp [hbe])
  · -- base invocation
    rw [hc']; dsimp only
    by_cases hpq : p = q
    · subst hpq
      simp only [Function.update_self]
      rcases hloc : ((𝒮).cfg lab n).loc p with _ | v | v | ⟨v, j, best⟩ <;>
        rw [hloc] at hp hact <;> rw [hpd, hbp] at hp <;> simp only [consImpl] at hact
      · cases hact
      · simp only [Action.call.injEq] at hact
        obtain ⟨rfl, rfl, rfl⟩ := hact
        obtain ⟨a', ha', h2, h3, h4, h5, -⟩ := hp
        cases ha'
        refine ⟨_, hpd, by omega, h3, h4, fun b hab hbn w => ?_, fun b hb => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hbn with hbn | rfl
          · exact h5 b hab hbn w
          · rw [hbe]; simp
        · cases hb; exact ⟨h2, by omega, hbe⟩
      · simp only [Action.call.injEq] at hact
        obtain ⟨rfl, rfl, rfl⟩ := hact
        obtain ⟨a', ha', h2, h3, h4, h5, -⟩ := hp
        cases ha'
        refine ⟨_, hpd, by omega, h3, h4, fun b hab hbn w hw => ?_, fun b hb => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hbn with hbn | rfl
          · exact absurd (h5 b hab hbn w hw) (by simp)
          · rfl
        · cases hb; exact ⟨h2, by omega, hbe⟩
      · split_ifs at hact with hj
        · simp only [Action.call.injEq] at hact
          obtain ⟨rfl, rfl, rfl⟩ := hact
          obtain ⟨a', ha', h2, h3, h4, h5, h6, h7, -⟩ := hp
          cases ha'
          refine ⟨_, hpd, by omega, h3, h4.mono (by omega), h5,
            fun hb y hy => (h6 hb y hy).mono (by omega), fun w hw => ?_, fun b hb => ?_⟩
          · obtain ⟨x, hx, hx1, hx2⟩ := h7 w hw
            exact ⟨x, hx, fun y hy => (hx1 y hy).mono (by omega), hx2.mono (by omega)⟩
          · cases hb; exact ⟨h2, by omega, h4, hj, hbe⟩
    · simp only [Function.update_of_ne hpq]
      exact hp.frame (by simp [he]) (by simp [hbe, Ne.symm hpq])
  · -- local step: impossible for pending processes
    rw [hc']; dsimp only
    by_cases hpq : p = q
    · subst hpq
      exfalso
      rcases hloc : ((𝒮).cfg lab n).loc p with _ | v | v | ⟨v, j, best⟩ <;>
        rw [hloc] at hp hact <;> rw [hpd] at hp <;> simp only [consImpl] at hact
      · exact absurd hp.1 (by simp)
      · cases hact
      · cases hact
      · split_ifs at hact
    · simp only [Function.update_of_ne hpq]
      exact hp.frame (by simp [he]) (by simp [hbe])
  · -- return
    rw [hc']; dsimp only
    by_cases hpq : p = q
    · subst hpq
      simp only [Function.update_self]
      rcases hloc : ((𝒮).cfg lab n).loc p with _ | v | v | ⟨v, j, best⟩ <;>
        rw [hloc] at hp hact <;> rw [hpd] at hp <;> simp only [consImpl] at hact
      · exact absurd hp.1 (by simp)
      · cases hact
      · cases hact
      · split_ifs at hact with hj
        simp only [Action.ret.injEq] at hact
        obtain ⟨-, rfl⟩ := hact
        obtain ⟨a', -, -, -, h4, -⟩ := hp
        exact ⟨rfl, hbp, fun _ => h4.mono (by omega)⟩
    · simp only [Function.update_of_ne hpq]
      exact hp.frame (by simp [he]) (by simp [hbe])
  · -- base response
    rw [hc']; dsimp only
    by_cases hpq : p = q
    · subst hpq
      simp only [Function.update_self]
      rcases hloc : ((𝒮).cfg lab n).loc p with _ | v | v | ⟨v, j, best⟩ <;>
        rw [hloc] at hp hact <;> rw [hbp] at hp <;> simp only [consImpl] at hact
      · cases hact
      · -- the read of the own register in line 2
        simp only [Action.call.injEq] at hact
        obtain ⟨rfl, rfl, rfl⟩ := hact
        obtain ⟨a, hpd, h2, h3, h4, h5, h6⟩ := hp
        obtain ⟨hab, hbn, hBb⟩ := h6 b rfl
        rcases r with _ | w
        · refine ⟨a, hpd, by omega, h3, fun hE => ?_, fun b2 hab2 hb2 w hw => ?_,
            fun b2 hb2 => by cases hb2⟩
          · exact hR2 b n p none hBb hbe ((h4 hE).mono (by omega)) rfl
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hb2 with hb2 | rfl
            · exact absurd hw (h5 b2 hab2 hb2 w)
            · rw [hbe] at hw; cases hw
        · refine ⟨a, hpd, by omega, h3, ?_, fun h => by omega, fun _ y hy => by omega,
            fun w' h => (by cases h), fun b2 hb2 => (by cases hb2)⟩
          obtain ⟨bw, hbw, q', hq'⟩ := hR1 b n p p w hBb hbe
          obtain ⟨hq, -⟩ := inv_write lab (hall bw (by omega)) hq'
          subst hq
          have hne : bw ≠ b := by rintro rfl; rw [hBb] at hq'; simp at hq'
          rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
          · obtain ⟨j, r', hj, hjr⟩ := hWF.seq bw b _ _ _ _ _ hq' hBb hlt
            exact ⟨bw, j, w, r', by omega, hq', hjr⟩
          · obtain ⟨j, r', hj, hjr⟩ := hWF.seq b bw _ _ _ _ _ hBb hq' hlt
            have := hWF.res_unique b j n r' (some w) hjr hbe
            omega
      · -- the write
        simp only [Action.call.injEq] at hact
        obtain ⟨rfl, rfl, rfl⟩ := hact
        obtain ⟨a, hpd, h2, h3, h4, h5, h6⟩ := hp
        obtain ⟨hab, hbn, hBb⟩ := h6 b rfl
        exact ⟨a, hpd, by omega, h3, ⟨b, n, v, r, by omega, hBb, hbe⟩, fun h => by omega,
          fun _ y hy => by omega, fun w' h => (by cases h), fun b2 hb2 => (by cases hb2)⟩
      · -- a read of the scan
        split_ifs at hact with hj
        · simp only [Action.call.injEq] at hact
          obtain ⟨rfl, rfl, rfl⟩ := hact
          obtain ⟨a, hpd, h2, h3, h4, h5, h6, h7, h8⟩ := hp
          obtain ⟨hab, hbn, hOw, hj', hBb⟩ := h8 b rfl
          refine ⟨a, hpd, by omega, h3, h4.mono (by omega), fun hpj => ?_, fun hn y hy => ?_,
            fun w hw => ?_, fun b2 hb2 => (by cases hb2)⟩
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hpj with hpj | hpj
            · cases best with
              | none => exact absurd rfl (h5 hpj)
              | some w => simp [consPick]
            · have hpx : (⟨j, hj⟩ : Fin N) = p := Fin.ext hpj.symm
              rw [hpx] at hBb
              have := hR2 b n p r hBb hbe hOw
              cases best with
              | none => simpa [consPick] using this
              | some w => simp [consPick]
          · cases best with
            | some w => simp [consPick] at hn
            | none =>
              simp only [consPick] at hn
              subst hn
              rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | hy
              · exact (h6 rfl y hy).mono (by omega)
              · have hyx : y = ⟨j, hj⟩ := Fin.ext hy
                subst hyx
                exact ⟨b, n, hab, by omega, hBb, hbe⟩
          · cases best with
            | some w' =>
              simp only [consPick, Option.some.injEq] at hw
              subst hw
              obtain ⟨x, hx, hx1, hx2⟩ := h7 w' rfl
              exact ⟨x, by omega, fun y hy => (hx1 y hy).mono (by omega), hx2.mono (by omega)⟩
            | none =>
              simp only [consPick] at hw
              subst hw
              exact ⟨⟨j, hj⟩, by simp, fun y hy => (h6 rfl y hy).mono (by omega),
                ⟨b, n, hab, by omega, hBb, hbe⟩⟩
    · simp only [Function.update_of_ne hpq]
      exact hp.frame (by simp [he]) (by simp [hbe])

section Adm

variable (hAdm : ELAdm (consImpl N D) (fun _ => regT D) lab)
include hAdm

lemma adm_R1 : ∀ b b' (q x : Fin N) w, (𝒮).bhist lab b = some (.inv q x .read) →
    (𝒮).bhist lab b' = some (.res b (some w)) →
    ∃ bw < b', ∃ q', (𝒮).bhist lab bw = some (.inv q' x (.write w)) := by
  intro b b' q x w hb hb'
  obtain ⟨bw, hbw, q', h⟩ := reg_wc_read_some (hAdm.2 x).1 (restrict_inv_iff.2 ⟨hb, rfl⟩)
    (restrict_res_iff.2 ⟨hb', q, _, hb⟩)
  exact ⟨bw, hbw, q', restrict_eq_some h⟩

lemma adm_R2 : ∀ b b' (p : Fin N) r, (𝒮).bhist lab b = some (.inv p p .read) →
    (𝒮).bhist lab b' = some (.res b r) → OwnW ((𝒮).bhist lab) p b → r ≠ none := by
  rintro b b' p r hb hb' ⟨bw, bw', v, r', hlt, hbw, hbw'⟩
  exact reg_wc_read_ne_none (hAdm.2 p).1 (restrict_inv_iff.2 ⟨hb, rfl⟩)
    (restrict_res_iff.2 ⟨hb', p, _, hb⟩) (restrict_inv_iff.2 ⟨hbw, rfl⟩)
    (restrict_res_iff.2 ⟨hbw', p, _, hbw⟩) hlt

/-- The invariant holds in every admissible execution. -/
theorem inv_all : ∀ n, Inv lab n := by
  have key : ∀ n, ∀ k ≤ n, Inv lab k := by
    intro n
    induction n with
    | zero => intro k hk; obtain rfl : k = 0 := by omega
              exact inv_zero lab
    | succ n ih =>
      intro k hk
      rcases Nat.le_succ_iff.1 hk with hk | rfl
      · exact ih k hk
      · exact inv_succ lab (el_wellFormed_bhist _ lab) (adm_R1 lab hAdm) (adm_R2 lab hAdm) ih
  exact fun n => key n n le_rfl

/-- At most one write per register. -/
lemma write_unique {b1 b2 : ℕ} {p1 p2 x : Fin N} {w1 w2 : D}
    (h1 : (𝒮).bhist lab b1 = some (.inv p1 x (.write w1)))
    (h2 : (𝒮).bhist lab b2 = some (.inv p2 x (.write w2))) : b1 = b2 := by
  have hI := inv_all lab hAdm
  wlog hlt : b1 < b2 generalizing b1 b2 p1 p2 w1 w2 with H
  · rcases lt_or_eq_of_le (not_lt.1 hlt) with h | h
    · exact (H h2 h1 h).symm
    · exact h.symm
  obtain ⟨hx1, a1, hpd1, -, hab1, hH1, -, -⟩ := inv_write lab (hI b1) h1
  obtain ⟨hx2, a2, hpd2, -, hab2, hH2, hE2, hW2⟩ := inv_write lab (hI b2) h2
  subst hx1 hx2
  rcases lt_trichotomy a1 a2 with h | rfl | h
  · exact absurd ⟨a1, h, w1, hH1⟩ hE2
  · exact absurd h1 (hW2 b1 hab1 hlt w1)
  · obtain ⟨j, r, hj, hjr⟩ := (el_wellFormed_hist _ lab).seq a2 a1 _ _ _ _ _ hH2 hH1 h
    have PI := pendInv_all (H := (𝒮).hist lab) (pend := fun n => ((𝒮).cfg lab n).pend)
      (fun _ => rfl) (el_pendStep _ lab) b2
    exact absurd hjr ((PI.pend_spec _ _ hpd2).2.2 j (by omega) r)

end Adm

/-- A completed operation returns the leftmost non-`⊥` value read in its scan. -/
lemma inv_res {m a : ℕ} {w : D} (hI : Inv lab m) (h : (𝒮).hist lab m = some (.res a w)) :
    ∃ p v, (𝒮).hist lab a = some (.inv p () v) ∧ ∃ x : Fin N,
      (∀ y : Fin N, y.val < x.val → ReadBy ((𝒮).bhist lab) p y none a m) ∧
      ReadBy ((𝒮).bhist lab) p x (some w) a m := by
  rcases el_step (consImpl N D) lab m with ⟨-, he, -, -⟩ | ⟨q, op, -, -, -, he, -⟩ |
    ⟨q, a', x, o, k, -, -, -, -, -, he, -⟩ | ⟨q, a', l', -, -, -, -, -, he, -⟩ |
    ⟨q, a', r, l', -, hpd, hbp, hact, -, he, -⟩ | ⟨q, r, b, x, o, k, -, -, -, -, he, -⟩
  all_goals rw [h] at he
  all_goals (try simp at he)
  obtain ⟨rfl, rfl⟩ := he
  have hp := hI q
  rcases hloc : ((𝒮).cfg lab m).loc q with _ | v | v | ⟨v, j, best⟩ <;>
    rw [hloc] at hp hact <;> simp only [consImpl] at hact
  · cases hact
  · cases hact
  · cases hact
  · split_ifs at hact with hj
    simp only [Action.ret.injEq] at hact
    obtain ⟨rfl, -⟩ := hact
    rw [hpd] at hp
    obtain ⟨a'', ha'', -, h3, -, h5, -, h7, -⟩ := hp
    cases ha''
    cases best with
    | none => exact absurd rfl (h5 (by omega))
    | some w' =>
      obtain ⟨x, -, hx1, hx2⟩ := h7 w' rfl
      exact ⟨q, v, h3, x, hx1, hx2⟩

/-- The consensus history of an admissible execution is weakly consistent: a completed
`Propose` returning `w` read `w` from some `Proposal[x]`, so `p_x` wrote `w` during a
`Propose(w)` operation `op₀` invoked before; `op₀` followed by the earlier operations of the
process and the operation itself, all returning `w`, is a legal witness. -/
theorem cons_weaklyConsistent (hAdm : ELAdm (consImpl N D) (fun _ => regT D) lab) :
    WeaklyConsistent (fun _ => consT D) ((𝒮).hist lab) := by
  classical
  intro a m w hm
  have hI := inv_all lab hAdm
  have hWF := el_wellFormed_hist (consImpl N D) lab
  obtain ⟨p, v, ha, x, -, b, b', hab, hb'm, hb, hb'⟩ := inv_res lab (hI m) hm
  obtain ⟨bw, hbw, q', hq'⟩ := adm_R1 lab hAdm b b' p x w hb hb'
  obtain ⟨-, a0, -, -, ha0bw, ha0, hE0, -⟩ := inv_write lab (hI bw) hq'
  have ham : a < m := (hWF.res_inv a m w hm).1
  have hprec : ∀ c, SameProc ((𝒮).hist lab) c a → Precedes ((𝒮).hist lab) c a →
      c < a ∧ ∃ v', (𝒮).hist lab c = some (.inv p () v') := by
    rintro c ⟨p1, x1, x1', op1, op1', hc, ha'⟩ ⟨j, r, hj, hja, -⟩
    rw [ha] at ha'
    simp only [Option.some.injEq, Ev.inv.injEq] at ha'
    obtain ⟨rfl, -, -⟩ := ha'
    have := (hWF.res_inv c j r hj).1
    exact ⟨by omega, op1, hc⟩
  by_cases h00 : a0 = a
  · subst h00
    have hpq : p = q' := by
      rw [ha] at ha0
      simp only [Option.some.injEq, Ev.inv.injEq] at ha0
      exact ha0.1
    subst hpq
    refine ⟨listSeq ([] ++ [a0]) w, listSeq_nodup (by simp), legal_cons (a0 := a0) (p0 := p)
      (by simp [listSeq]) ha0 fun k c r hk => ?_, fun c hc => ?_, fun c hc1 hc2 => ?_,
      listSeq_last⟩
    · obtain ⟨h1, rfl⟩ := listSeq_eq_some.1 hk
      have : c = a0 := by simpa using List.mem_of_getElem? h1
      subst this
      exact ⟨rfl, p, (), v, ha⟩
    · have : c = a0 := by simpa using listSeq_mem.1 hc
      omega
    · obtain ⟨hca, v', hc⟩ := hprec c hc1 hc2
      exact absurd ⟨c, hca, v', hc⟩ hE0
  · set L := ((Finset.range a).filter
      (fun c => c ≠ a0 ∧ ∃ v', (𝒮).hist lab c = some (.inv p () v'))).toList with hL
    have hmemL : ∀ c, c ∈ L ↔ c < a ∧ c ≠ a0 ∧ ∃ v', (𝒮).hist lab c = some (.inv p () v') := by
      intro c; simp [hL]
    have hnd : (a0 :: L ++ [a]).Nodup := by
      rw [List.cons_append, List.nodup_cons, List.nodup_append]
      refine ⟨fun h => ?_, Finset.nodup_toList _, List.nodup_singleton a, fun c hc d hd => ?_⟩
      · rcases List.mem_append.1 h with h | h
        · exact ((hmemL a0).1 h).2.1 rfl
        · exact h00 (List.mem_singleton.1 h)
      · rw [List.mem_singleton] at hd; subst hd
        have := ((hmemL c).1 hc).1; omega
    have hent : ∀ c, c ∈ a0 :: L ++ [a] → Invoked ((𝒮).hist lab) c ∧ c < m := by
      intro c hc
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | hc | rfl
      · have := (el_wellFormed_bhist _ lab).res_inv b b' _ hb'
        exact ⟨⟨q', (), w, ha0⟩, by omega⟩
      · obtain ⟨h1, -, v', h2⟩ := (hmemL c).1 hc
        exact ⟨⟨p, (), v', h2⟩, by omega⟩
      · exact ⟨⟨p, (), v, ha⟩, ham⟩
    refine ⟨listSeq (a0 :: L ++ [a]) w, listSeq_nodup hnd, legal_cons (a0 := a0) (p0 := q')
      (by simp [listSeq]) ha0 fun k c r hk => ?_, fun c hc => (hent c (listSeq_mem.1 hc)).2,
      fun c hc1 hc2 => ?_, listSeq_last⟩
    · obtain ⟨h1, rfl⟩ := listSeq_eq_some.1 hk
      exact ⟨rfl, (hent c (List.mem_of_getElem? h1)).1⟩
    · obtain ⟨hca, v', hc⟩ := hprec c hc1 hc2
      rw [listSeq_mem]
      by_cases hc0 : c = a0
      · subst hc0; simp
      · simp only [List.cons_append, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl ((hmemL c).2 ⟨hca, hc0, v', hc⟩))

lemma consT_total : (consT D).Total := by
  intro q v
  cases q with
  | none => exact ⟨v, some v, Or.inl ⟨rfl, rfl, rfl⟩⟩
  | some r => exact ⟨r, some r, Or.inr ⟨rfl, rfl⟩⟩

/-- The consensus history of an admissible execution is `t`-linearizable for some `t`. Each
register `x` eventually returns a fixed value `fin x` to all reads (it is written at most once,
by `p_x`); operations invoked after that time `T` return the leftmost non-`⊥` `fin x`, i.e. the
same value `w`, proposed by the operation `op₀` that wrote it. -/
theorem cons_exists_tLin (hAdm : ELAdm (consImpl N D) (fun _ => regT D) lab) :
    ∃ t, TLinearizable (fun _ => consT D) ((𝒮).hist lab) t := by
  classical
  have hI := inv_all lab hAdm
  have hWF := el_wellFormed_hist (consImpl N D) lab
  have hWFB := el_wellFormed_bhist (consImpl N D) lab
  -- each register stabilizes
  have hreg : ∀ x : Fin N, ∃ T fin, (∀ b b' (q : Fin N) r,
      (𝒮).bhist lab b = some (.inv q x .read) → (𝒮).bhist lab b' = some (.res b r) → T ≤ b' →
      r = fin) ∧ (∀ w, fin = some w → ∃ bw, ∃ q : Fin N,
        (𝒮).bhist lab bw = some (.inv q x (.write w))) := by
    intro x
    obtain ⟨tx, Sx, hSx⟩ := (hAdm.2 x).2
    obtain ⟨T, fin, h1, h2⟩ := reg_stable (hWFB.restrict x) hSx
      (fun b1 b2 p1 p2 w1 w2 hb1 hb2 => write_unique lab hAdm (restrict_eq_some hb1)
        (restrict_eq_some hb2))
    refine ⟨T, fin, fun b b' q r hb hb' hT => h1 b b' q r (restrict_inv_iff.2 ⟨hb, rfl⟩)
      (restrict_res_iff.2 ⟨hb', q, _, hb⟩) hT, fun w hw => ?_⟩
    obtain ⟨bw, q, hbw⟩ := h2 w hw
    exact ⟨bw, q, restrict_eq_some hbw⟩
  choose Tx fin hfin hfinw using hreg
  set T := Finset.univ.sup Tx with hTdef
  have hTx : ∀ x, Tx x ≤ T := fun x => Finset.le_sup (Finset.mem_univ x)
  -- operations invoked at `≥ T` return the leftmost non-`⊥` final value
  have hlate : ∀ a m w, (𝒮).hist lab m = some (.res a w) → T ≤ a →
      ∃ x : Fin N, fin x = some w ∧ ∀ y : Fin N, y.val < x.val → fin y = none := by
    intro a m w hm haT
    obtain ⟨p, v, -, x, hx1, b, b', hab, -, hb, hb'⟩ := inv_res lab (hI m) hm
    have hbb' := (hWFB.res_inv b b' _ hb').1
    refine ⟨x, (hfin x b b' p _ hb hb' (by have := hTx x; omega)).symm, fun y hy => ?_⟩
    obtain ⟨c, c', hac, -, hc, hc'⟩ := hx1 y hy
    have hcc' := (hWFB.res_inv c c' _ hc').1
    exact (hfin y c c' p _ hc hc' (by have := hTx y; omega)).symm
  have huniq : ∀ a m w a' m' w', (𝒮).hist lab m = some (.res a w) → T ≤ a →
      (𝒮).hist lab m' = some (.res a' w') → T ≤ a' → w = w' := by
    intro a m w a' m' w' hm ha hm' ha'
    obtain ⟨x, hx, hx'⟩ := hlate a m w hm ha
    obtain ⟨y, hy, hy'⟩ := hlate a' m' w' hm' ha'
    rcases lt_trichotomy x.val y.val with h | h | h
    · rw [hy' x h] at hx; cases hx
    · rw [Fin.ext h, hy] at hx; cases hx; rfl
    · rw [hx' y h] at hy; cases hy
  obtain ⟨M, hM⟩ := exists_resp_bound_gen hWF T
  by_cases hex : ∃ a m w, (𝒮).hist lab m = some (.res a w) ∧ T ≤ a
  · obtain ⟨a₁, m₁, w₀, hm₁, ha₁⟩ := hex
    obtain ⟨x₀, hx₀, -⟩ := hlate a₁ m₁ w₀ hm₁ ha₁
    obtain ⟨bw, q, hbw⟩ := hfinw x₀ w₀ hx₀
    obtain ⟨-, a₀, -, -, -, ha₀, -, -⟩ := inv_write lab (hI bw) hbw
    refine ⟨max (max T (a₀ + 1)) M, fun k => if k = 0 then some (a₀, w₀) else
      match (𝒮).hist lab (k - 1) with
      | some (.res c _) => if c = a₀ then none else some (c, w₀)
      | _ => none, ?_⟩
    set S : SeqHist D := fun k => if k = 0 then some (a₀, w₀) else
      match (𝒮).hist lab (k - 1) with
      | some (.res c _) => if c = a₀ then none else some (c, w₀)
      | _ => none with hS
    -- the entries of `S`
    have hSk : ∀ k c r, S k = some (c, r) → r = w₀ ∧ ((k = 0 ∧ c = a₀) ∨
        (k ≠ 0 ∧ c ≠ a₀ ∧ ∃ r', (𝒮).hist lab (k - 1) = some (.res c r'))) := by
      intro k c r hk
      by_cases hk0 : k = 0
      · subst hk0
        simp only [hS, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hk
        exact ⟨hk.2.symm, Or.inl ⟨rfl, hk.1.symm⟩⟩
      · simp only [hS, hk0, ↓reduceIte] at hk
        split at hk
        · rename_i c' r' he
          split_ifs at hk with hc'
          simp only [Option.some.injEq, Prod.mk.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk
          exact ⟨rfl, Or.inr ⟨hk0, hc', r', he⟩⟩
        · cases hk
    have hSres : ∀ j c r, (𝒮).hist lab j = some (.res c r) → c ≠ a₀ → S (j + 1) = some (c, w₀) := by
      intro j c r hj hc
      simp only [hS, Nat.add_sub_cancel, hj]
      simp [hc]
    refine ⟨fun k k' c r r' hk hk' => ?_, legal_cons (by simp [hS]) ha₀ fun k c r hk => ?_,
      fun c j r hj => ?_, fun c b j r hj htj hjb hbinv hbmem => ?_, fun c j r hj htj => ?_⟩
    · -- nodup
      obtain ⟨-, h1⟩ := hSk k c r hk
      obtain ⟨-, h2⟩ := hSk k' c r' hk'
      rcases h1 with ⟨rfl, rfl⟩ | ⟨hk0, hca, r1, h1⟩ <;> rcases h2 with ⟨rfl, h2⟩ | ⟨hk0', hca', r2, h2⟩
      · rfl
      · exact absurd rfl hca'
      · exact absurd h2 hca
      · have := hWF.res_unique _ _ _ _ _ h1 h2; omega
    · obtain ⟨hr, h1⟩ := hSk k c r hk
      refine ⟨hr, ?_⟩
      rcases h1 with ⟨-, rfl⟩ | ⟨-, -, r1, h1⟩
      · exact ⟨q, (), w₀, ha₀⟩
      · exact (hWF.res_inv _ _ _ h1).2
    · -- complete
      by_cases hc : c = a₀
      · subst hc; exact ⟨0, w₀, by simp [hS]⟩
      · exact ⟨j + 1, w₀, hSres j c r hj hc⟩
    · -- real-time order
      obtain ⟨kb, rb, hkb⟩ := hbmem
      obtain ⟨-, h1⟩ := hSk kb b rb hkb
      rcases h1 with ⟨-, rfl⟩ | ⟨hkb0, -, r1, h1⟩
      · omega
      · have hb1 := (hWF.res_inv _ _ _ h1).1
        by_cases hc : c = a₀
        · subst hc
          exact ⟨0, kb, w₀, rb, by omega, by simp [hS], hkb⟩
        · exact ⟨j + 1, kb, w₀, rb, by omega, hSres j c r hj hc, hkb⟩
    · -- responses after `t`
      have hcT : T ≤ c := by
        by_contra h
        have := hM c (by omega) j r hj
        omega
      have hr := huniq a₁ m₁ w₀ c j r hm₁ ha₁ hj hcT
      subst hr
      by_cases hc : c = a₀
      · subst hc; exact ⟨0, by simp [hS]⟩
      · exact ⟨j + 1, hSres j c _ hj hc⟩
  · push Not at hex
    refine ⟨M, tLinearizable_of_no_late (fun _ => ⟨none, Set.mem_singleton _⟩) (fun _ => consT_total) hWF
      fun j a r hj => ?_⟩
    exact hM a (hex a j r hj) j r hj

/-- The progress measure of a process: `2 · (remaining base accesses) + [no pending base op]`. -/
def meas (N : ℕ) : CLoc D → Option ℕ → ℕ
  | .idle, _ => 0
  | .chk _, bp => 2 * (N + 2) + if bp = none then 1 else 0
  | .wr _, bp => 2 * (N + 1) + if bp = none then 1 else 0
  | .scan _ j _, bp => 2 * (N - j) + if bp = none then 1 else 0

/-- One step of a process `p` with a pending operation `a` that never completes: `a` stays
pending, and the measure does not increase, and decreases if `p` takes the step. -/
lemma wf_step (hP : (𝒮).Proper lab) {n a : ℕ} {p : Fin N} (hI : Inv lab n)
    (hpd : ((𝒮).cfg lab n).pend p = some a) (hnc : ¬ Completed ((𝒮).hist lab) a) :
    ((𝒮).cfg lab (n + 1)).pend p = some a ∧
      meas N (((𝒮).cfg lab (n + 1)).loc p) (((𝒮).cfg lab (n + 1)).bpend p) ≤
        meas N (((𝒮).cfg lab n).loc p) (((𝒮).cfg lab n).bpend p) ∧
      (LSys.StepBy ELab.proc lab n p →
        meas N (((𝒮).cfg lab (n + 1)).loc p) (((𝒮).cfg lab (n + 1)).bpend p) <
          meas N (((𝒮).cfg lab n).loc p) (((𝒮).cfg lab n).bpend p)) := by
  have hp := hI p
  rcases el_step (consImpl N D) lab n with ⟨hc', he, hbe, hdis⟩ | ⟨q, op, hl, hqd, hc', he, hbe⟩ |
    ⟨q, a', x, o, k, hl, hqd, hbp, hact, hc', he, hbe⟩ | ⟨q, a', l', hl, hqd, hbp, hact, hc', he, hbe⟩ |
    ⟨q, a', r, l', hl, hqd, hbp, hact, hc', he, hbe⟩ | ⟨q, r, b, x, o, k, hl, hbp, hact, hc', he, hbe⟩
  · rw [hc']
    refine ⟨hpd, le_rfl, fun ⟨l, hl, _⟩ => absurd (hdis l hl) (hP n l hl)⟩
  · have hpq : p ≠ q := by rintro rfl; rw [hpd] at hqd; cases hqd
    rw [hc']; dsimp only
    simp only [Function.update_of_ne hpq]
    refine ⟨hpd, le_rfl, fun ⟨l, hl', hlp⟩ => ?_⟩
    rw [hl] at hl'; cases hl'; exact absurd hlp.symm hpq
  · rw [hc']; dsimp only
    by_cases hpq : p = q
    · subst hpq
      simp only [Function.update_self]
      have hlt : meas N (((𝒮).cfg lab n).loc p) (some n) <
          meas N (((𝒮).cfg lab n).loc p) (((𝒮).cfg lab n).bpend p) := by
        rw [hbp]
        rcases hloc : ((𝒮).cfg lab n).loc p with _ | v | v | ⟨v, j, best⟩
        · rw [hloc] at hact; simp [consImpl] at hact
        all_goals simp [meas]
      exact ⟨hpd, hlt.le, fun _ => hlt⟩
    · simp only [Function.update_of_ne hpq]
      refine ⟨hpd, le_rfl, fun ⟨l, hl', hlp⟩ => ?_⟩
      rw [hl] at hl'; cases hl'; exact absurd hlp.symm hpq
  · rw [hc']; dsimp only
    by_cases hpq : p = q
    · subst hpq
      exfalso
      rcases hloc : ((𝒮).cfg lab n).loc p with _ | v | v | ⟨v, j, best⟩ <;>
        rw [hloc] at hp hact <;> simp only [consImpl] at hact
      · rw [hpd] at hp; exact absurd hp.1 (by simp)
      · cases hact
      · cases hact
      · split_ifs at hact
    · simp only [Function.update_of_ne hpq]
      refine ⟨hpd, le_rfl, fun ⟨l, hl', hlp⟩ => ?_⟩
      rw [hl] at hl'; cases hl'; exact absurd hlp.symm hpq
  · rw [hc']; dsimp only
    by_cases hpq : p = q
    · subst hpq
      rw [hpd] at hqd; cases hqd
      exact absurd ⟨n, r, he⟩ hnc
    · simp only [Function.update_of_ne hpq]
      refine ⟨hpd, le_rfl, fun ⟨l, hl', hlp⟩ => ?_⟩
      rw [hl] at hl'; cases hl'; exact absurd hlp.symm hpq
  · rw [hc']; dsimp only
    by_cases hpq : p = q
    · subst hpq
      simp only [Function.update_self]
      have hlt : meas N (k r) none < meas N (((𝒮).cfg lab n).loc p) (((𝒮).cfg lab n).bpend p) := by
        rw [hbp]
        rcases hloc : ((𝒮).cfg lab n).loc p with _ | v | v | ⟨v, j, best⟩ <;>
          rw [hloc] at hact <;> simp only [consImpl] at hact
        · cases hact
        · simp only [Action.call.injEq] at hact
          obtain ⟨-, -, rfl⟩ := hact
          cases r <;> simp [meas] <;> omega
        · simp only [Action.call.injEq] at hact
          obtain ⟨-, -, rfl⟩ := hact
          simp [meas]; omega
        · split_ifs at hact with hj
          simp only [Action.call.injEq] at hact
          obtain ⟨-, -, rfl⟩ := hact
          simp [meas]; omega
      exact ⟨hpd, hlt.le, fun _ => hlt⟩
    · simp only [Function.update_of_ne hpq]
      refine ⟨hpd, le_rfl, fun ⟨l, hl', hlp⟩ => ?_⟩
      rw [hl] at hl'; cases hl'; exact absurd hlp.symm hpq

end Exec

end Prop16

section Main

open Prop16

variable {N : ℕ} {D : Type}

local notation "𝒮" => elSys (consImpl N D)

/-- The algorithm is wait-free: an operation of a process taking infinitely many steps
completes (after at most `2N + 6` steps of the process). -/
theorem cons_waitFree : (𝒮).WaitFree ELab.proc (ELAdm (consImpl N D) (fun _ => regT D)) := by
  intro lab hAdm a p op ha hinf
  by_contra hnc
  have hI := inv_all lab hAdm
  have h0 : ((𝒮).cfg lab (a + 1)).pend p = some a := by
    rcases el_step (consImpl N D) lab a with ⟨-, he, -, -⟩ | ⟨q, op', -, -, hc', he, -⟩ |
      ⟨q, a', x, o, k, -, -, -, -, -, he, -⟩ | ⟨q, a', l', -, -, -, -, -, he, -⟩ |
      ⟨q, a', r, l', -, -, -, -, -, he, -⟩ | ⟨q, r, b, x, o, k, -, -, -, -, he, -⟩
    all_goals rw [ha] at he
    all_goals (try simp at he)
    obtain ⟨rfl, -⟩ := he
    rw [hc']
    simp
  have hpend : ∀ n, a + 1 ≤ n → ((𝒮).cfg lab n).pend p = some a := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact h0
    | succ n hn ih => exact (wf_step lab hAdm.1 (hI n) ih hnc).1
  let μ : ℕ → ℕ := fun n => meas N (((𝒮).cfg lab n).loc p) (((𝒮).cfg lab n).bpend p)
  have hmono : ∀ n m, a + 1 ≤ n → n ≤ m → μ m ≤ μ n := by
    intro n m hn hm
    induction m, hm using Nat.le_induction with
    | base => exact le_rfl
    | succ m hm ih => exact (wf_step lab hAdm.1 (hI m) (hpend m (by omega)) hnc).2.1.trans ih
  have key : ∀ k, ∃ n, a + 1 ≤ n ∧ μ n + k ≤ μ (a + 1) := by
    intro k
    induction k with
    | zero => exact ⟨a + 1, le_rfl, by omega⟩
    | succ k ih =>
      obtain ⟨n, hn, hk⟩ := ih
      obtain ⟨n', hn', hstep⟩ := hinf n
      have h1 := (wf_step lab hAdm.1 (hI n') (hpend n' (by omega)) hnc).2.2 hstep
      have h2 := hmono n n' hn hn'
      exact ⟨n' + 1, by omega, by simp only [μ] at h1 h2 hk ⊢; omega⟩
  obtain ⟨n, -, hn⟩ := key (μ (a + 1) + 1)
  omega

/-- **Proposition 16** of [Guerraoui–Ruppert, PODC 2014]. A consensus object has a wait-free,
eventually linearizable implementation from eventually linearizable registers: the algorithm
`consImpl` (for `N` processes, registers `Proposal[0..N-1]` initially `⊥`), run over base
registers whose histories are eventually linearizable (`ELAdm`), is wait-free and every
admissible consensus history is eventually linearizable. -/
theorem prop16 (n : ℕ) (D : Type) :
    (elSys (consImpl n D)).WaitFree ELab.proc (ELAdm (consImpl n D) (fun _ => regT D)) ∧
    (elSys (consImpl n D)).IsEventuallyLinearizable (ELAdm (consImpl n D) (fun _ => regT D))
      (consT D) :=
  ⟨cons_waitFree, fun lab hAdm => ⟨cons_weaklyConsistent lab hAdm, cons_exists_tLin lab hAdm⟩⟩

end Main

end Podc.EventualLinParadox
