import Cslib.Computability.Distributed.MessagePassing.Async
import Papers.PODC2020.FastMWMRImpossibility.Lin

/-!
# The W2R1 algorithm of §5.2 / Appendix A (Algorithms 1 and 2) is not atomic

The paper's fast-read multi-writer algorithm, as an asynchronous message-passing protocol
(`Cslib.AsyncMP`), for `S = 4` servers, `t = 1`, `R = 1` reader and `W = 2` writers. The paper
claims it is atomic whenever `R < S/t − 2` (here `1 < 2`). We exhibit a reachable execution with a
non-linearizable history (`w2r1_not_linearizable`): a read that starts after `write(1)` returned
returns the initial value `0`. This contradicts property MWA2 / Lemma 5.

**The algorithm** (Algorithms 1–2), values tagged `(ts, wid)` and ordered lexicographically.
* A server keeps a `valuevector`: for each tagged value it received, the set `updated` of clients
  that have been recorded with it. `update(val, c)` adds `c` to `updated[val]` (creating the
  entry if needed; if `val` exceeds the current value this is line 9–11).
* A writer queries all servers for their current timestamp (first round-trip). It writes
  `(maxTS + 1, wid)` to all servers (second round-trip), waiting for `S − t` replies each time.
* A reader sends `(read, valQueue)`. A server does `update(val, r)` for every `val` in `valQueue`
  (line 20) and replies with its `valuevector`. The reader waits for `S − t` replies and returns
  the largest value `v` that is `admissible(v, rcvMsg, a)` for some `a ∈ [1, R + 1]`: some set `μ`
  of replies, all containing `v`, with `|μ| ≥ S − a t` and `|⋂_{m ∈ μ} m.updated(v)| ≥ a` (lines
  23–32).

The pseudo-code is ambiguous on one point: does a read request also record the reader with the
server's *current* value, as in the single-writer algorithm of Dutta et al. that the paper extends?
The flag `markCur` covers both readings. The counterexample works for both.

**The execution.**
1. `w₁` and `w₂` both query and see `ts = 0`, so they write `(1, w₁)` (value `1`) and `(1, w₂)`
   (value `2`).
2. `(1, w₁)` reaches `s₀, s₁, s₂`, and `write(1)` returns.
3. The read is invoked. `(1, w₂)` reaches `s₀` and `s₁`.
4. The read request reaches `s₀, s₂, s₃`, and the reader uses these three replies.
   * `(1, w₂)` is only in `s₀`'s reply, so it is not admissible (`a = 3` would be needed).
   * `(1, w₁)` is in the replies of `s₀` and `s₂`, but at `s₀` its `updated` set is `{w₁}`. The
     reader was not recorded there: `(1, w₁)` is neither in its `valQueue` nor `s₀`'s current
     value. So the intersection is `{w₁}` and the value is not admissible with `a = 2`.
   * The read returns the initial value.
-/

namespace Podc.FastMWMR.W2R1

open Cslib.SharedMemory Cslib.AsyncMP

/-- Processes: servers `s₀, …, s₃`, writers `w₁, w₂` (`wr 0`, `wr 1`), one reader. -/
inductive Node where
  | srv (s : Fin 4)
  | wr (i : Fin 2)
  | rd
  deriving DecidableEq

/-- Client identifiers used in the `updated` sets (writer ids are `1, 2`). -/
def Node.cid : Node → ℕ
  | .srv _ => 0
  | .wr i => i.val + 1
  | .rd => 3

/-- A tagged value `(ts, wid, v)`. -/
abbrev TV := ℕ × ℕ × ℕ

/-- The order on tagged values: lexicographic on `(ts, wid)`. -/
def TV.lt (x y : TV) : Bool := x.1 < y.1 || (x.1 == y.1 && x.2.1 < y.2.1)

/-- The initial tagged value `(0, ⊥)` with the initial register value `0`. -/
def tv₀ : TV := (0, 0, 0)

/-- A `valuevector`: tagged values with their `updated` sets. -/
abbrev VVec := List (TV × List ℕ)

/-- The current value `val_i` (the largest tagged value). -/
def VVec.cur (vv : VVec) : TV := vv.foldl (fun m e => if TV.lt m e.1 then e.1 else m) tv₀

/-- `update(val, c)` (Algorithm 2, lines 7–15). -/
def VVec.update (vv : VVec) (v : TV) (c : ℕ) : VVec :=
  if vv.any (fun e => e.1 == v) then
    vv.map fun e => if e.1 == v then (e.1, if c ∈ e.2 then e.2 else e.2 ++ [c]) else e
  else vv ++ [(v, [c])]

/-- The `updated` set of `v` in a reply (empty if `v` is absent). -/
def VVec.upd (vv : VVec) (v : TV) : List ℕ :=
  ((vv.find? fun e => e.1 == v).map Prod.snd).getD []

/-- The reply contains `v`. -/
def VVec.has (vv : VVec) (v : TV) : Bool := vv.any fun e => e.1 == v

/-- `⋂_{m ∈ μ} m.updated(v)`. -/
def inter (μ : List VVec) (v : TV) : List ℕ :=
  match μ with
  | [] => []
  | m :: rest => rest.foldl (fun acc m' => acc.filter fun c => c ∈ m'.upd v) (m.upd v)

/-- `admissible(v, Msg, a)` (Algorithm 1, line 32) with `S = 4`, `t = 1`. -/
def admissible (v : TV) (ms : List VVec) (a : ℕ) : Bool :=
  ms.sublists.any fun μ => μ.all (fun m => m.has v) && decide (4 ≤ μ.length + a * 1) &&
    decide (a ≤ (inter μ v).length)

/-- The value returned by a read with replies `ms` (lines 23–31, `R = 1`): the largest value that
is admissible with some degree `a ∈ [1, R + 1]`. -/
def decideRead (ms : List VVec) : TV :=
  (ms.flatMap fun m => m.map Prod.fst).foldl
    (fun b k => if (admissible k ms 1 || admissible k ms 2) && TV.lt b k then k else b) tv₀

/-- Messages (tagged with the client's operation counter `k`). -/
inductive Msg where
  | query (k : ℕ)
  | qack (k : ℕ) (ts : ℕ)
  | write (k : ℕ) (v : TV)
  | wack (k : ℕ)
  | read (k : ℕ) (vq : List TV)
  | rack (k : ℕ) (snap : VVec)
  deriving DecidableEq

/-- Writer control positions. -/
inductive WPh where
  | idle
  /-- first round-trip of `write(v)`: timestamps received -/
  | query (v : ℕ) (acks : List ℕ)
  /-- second round-trip: number of acknowledgements -/
  | write (v : ℕ) (acks : ℕ)

/-- Reader control positions. -/
inductive RPh where
  | idle
  | wait (msgs : List VVec)

/-- Local states. -/
inductive Loc where
  | srv (vv : VVec)
  | wr (k : ℕ) (ph : WPh)
  | rd (k : ℕ) (vq : List TV) (ph : RPh)

/-- Broadcast a message to the four servers. -/
def bcast (m : Msg) : Multiset (Node × Msg) :=
  (((List.finRange 4).map fun s => (Node.srv s, m)) : List (Node × Msg))

/-- Algorithms 1–2 as an asynchronous message-passing protocol (`S = 4`, `t = 1`, `R = 1`,
`W = 2`), implementing `register ℕ 0`. `markCur`: a read request also records the reader with the
server's current value (the reading closest to the single-writer algorithm of Dutta et al.);
`markCur = false` is the literal pseudo-code (line 20). -/
def protocol (markCur : Bool) : Protocol Node (register ℕ 0) Loc Msg Unit where
  init
    | .srv _ => .srv [(tv₀, [])]
    | .wr _ => .wr 0 .idle
    | .rd => .rd 0 [tv₀] .idle
  invoke p o l :=
    match p, o, l with
    | .wr _, .write v, .wr k .idle => some (.wr (k + 1) (.query v []), bcast (.query (k + 1)))
    | .rd, .read, .rd k vq .idle => some (.rd (k + 1) vq (.wait []), bcast (.read (k + 1) vq))
    | _, _, _ => none
  internal p _ l :=
    match p, l with
    | .wr i, .wr k (.query v acks) =>
      if 4 ≤ acks.length + 1 then
        some (.wr k (.write v 0), bcast (.write k (acks.foldl max 0 + 1, i.val + 1, v)), none)
      else none
    | .wr _, .wr k (.write v acks) =>
      if 4 ≤ acks + 1 then some (.wr k .idle, 0, some v) else none
    | .rd, .rd k vq (.wait ms) =>
      if 4 ≤ ms.length + 1 then
        some (.rd k (vq ++ (ms.flatMap fun m => m.map Prod.fst)) .idle, 0,
          some (decideRead ms).2.2)
      else none
    | _, _ => none
  receive p q m l :=
    match p, m, l with
    | .srv _, .query k, .srv vv => some (.srv vv, {(q, .qack k vv.cur.1)}, none)
    | .srv _, .write k v, .srv vv => some (.srv (vv.update v q.cid), {(q, .wack k)}, none)
    | .srv _, .read k vq, .srv vv =>
      let vv' := vq.foldl (fun w x => w.update x q.cid) vv
      let vv'' := if markCur then vv'.update vv'.cur q.cid else vv'
      some (.srv vv'', {(q, .rack k vv'')}, none)
    | .wr _, .qack k' ts, .wr k (.query v acks) =>
      some (if k' = k then .wr k (.query v (acks ++ [ts])) else l, 0, none)
    | .wr _, .wack k', .wr k (.write v acks) =>
      some (if k' = k then .wr k (.write v (acks + 1)) else l, 0, none)
    | .rd, .rack k' snap, .rd k vq (.wait ms) =>
      some (if k' = k then .rd k vq (.wait (ms ++ [snap])) else l, 0, none)
    | _, _, l => some (l, 0, none)

/-- Run a list of steps. -/
def run (Pr : Protocol Node (register ℕ 0) Loc Msg Unit) :
    Config Node Loc Msg → List (Step Node (register ℕ 0) Msg Unit) →
      Option (Config Node Loc Msg × List (Label Node (register ℕ 0)))
  | C, [] => some (C, [])
  | C, s :: ss => (Pr.step C s).bind fun x => (run Pr x.1 ss).map fun y => (y.1, x.2.toList ++ y.2)

lemma reach_of_run (Pr : Protocol Node (register ℕ 0) Loc Msg Unit) :
    ∀ (ss : List (Step Node (register ℕ 0) Msg Unit)) (C C' : Config Node Loc Msg) h hs,
      Pr.Reach C h → run Pr C ss = some (C', hs) → Pr.Reach C' (h ++ hs) := by
  intro ss
  induction ss with
  | nil => intro C C' h hs hR he; simp only [run, Option.some.injEq, Prod.mk.injEq] at he
           obtain ⟨rfl, rfl⟩ := he; simpa using hR
  | cons s ss ih =>
    intro C C' h hs hR he
    simp only [run, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
    obtain ⟨⟨C₁, ℓ⟩, h₁, ⟨C₂, hs₂⟩, h₂, he⟩ := he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have := ih C₁ C₂ _ hs₂ (Protocol.Reach.step hR h₁) h₂
    simpa using this

/-! ### The execution -/

/-- Messages of the execution. -/
def mW₁ : TV := (1, 1, 1)
def mW₂ : TV := (1, 2, 2)

/-- Replies to the read (contents depend on the reading `markCur`). -/
def snap₀ (mc : Bool) : VVec :=
  [(tv₀, [3]), (mW₁, [1]), (mW₂, if mc then [2, 3] else [2])]
def snap₂ (mc : Bool) : VVec := [(tv₀, [3]), (mW₁, if mc then [1, 3] else [1])]
def snap₃ : VVec := [(tv₀, [3])]

/-- The schedule. -/
def sched (mc : Bool) : List (Step Node (register ℕ 0) Msg Unit) :=
  -- both writers query `s₀, s₁, s₂` and see timestamp 0
  [.inv (.wr 0) (.write 1)] ++
  [0, 1, 2].map (fun s : Fin 4 => .recv (.wr 0) (.srv s) (.query 1)) ++
  [0, 1, 2].map (fun s : Fin 4 => .recv (.srv s) (.wr 0) (.qack 1 0)) ++
  [.internal (.wr 0) (), .inv (.wr 1) (.write 2)] ++
  [0, 1, 2].map (fun s : Fin 4 => .recv (.wr 1) (.srv s) (.query 1)) ++
  [0, 1, 2].map (fun s : Fin 4 => .recv (.srv s) (.wr 1) (.qack 1 0)) ++
  [.internal (.wr 1) ()] ++
  -- `(1, w₁)` reaches `s₀, s₁, s₂`; `write(1)` returns
  [0, 1, 2].map (fun s : Fin 4 => .recv (.wr 0) (.srv s) (.write 1 mW₁)) ++
  [0, 1, 2].map (fun s : Fin 4 => .recv (.srv s) (.wr 0) (.wack 1)) ++
  [.internal (.wr 0) (), .inv .rd .read] ++
  -- `(1, w₂)` reaches `s₀, s₁`
  [0, 1].map (fun s : Fin 4 => .recv (.wr 1) (.srv s) (.write 1 mW₂)) ++
  -- the read request reaches `s₀, s₂, s₃`; the reader uses their replies
  [0, 2, 3].map (fun s : Fin 4 => .recv .rd (.srv s) (.read 1 [tv₀])) ++
  [.recv (.srv 0) .rd (.rack 1 (snap₀ mc)), .recv (.srv 2) .rd (.rack 1 (snap₂ mc)),
    .recv (.srv 3) .rd (.rack 1 snap₃), .internal .rd ()]

/-- The history of the execution. -/
def hist : List (Label Node (register ℕ 0)) :=
  [.inv (.wr 0) (.write 1), .inv (.wr 1) (.write 2), .ret (.wr 0) 1, .inv .rd .read, .ret .rd 0]

/-- An injective encoding of labels into a type with decidable equality. -/
def enc : Label Node (register ℕ 0) → ℕ × Node × Option (RWOp ℕ) × ℕ
  | .inv p o => (0, p, some o, 0)
  | .ret p r => (1, p, none, r)
  | .tau p => (2, p, none, 0)

lemma enc_injective : Function.Injective enc := by
  intro x y h
  cases x <;> cases y <;> simp_all [enc]

lemma run_eq (mc : Bool) :
    ((run (protocol mc) (protocol mc).initCfg (sched mc)).map fun x => x.2.map enc) =
      some (hist.map enc) := by
  cases mc <;> decide

/-- The execution is reachable. -/
lemma reach_hist (mc : Bool) : ∃ C, (protocol mc).Reach C hist := by
  have h := run_eq mc
  rcases hrun : run (protocol mc) (protocol mc).initCfg (sched mc) with _ | ⟨C, hs⟩
  · rw [hrun] at h; simp at h
  · rw [hrun] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have : hs = hist := (List.map_injective_iff.2 enc_injective) h
    subst this
    exact ⟨C, by simpa using reach_of_run _ _ _ _ _ _ Protocol.Reach.init hrun⟩

/-- After a list of register operations containing a write, the state is the value of one of
these writes. -/
lemma runOps_eq_write (ops : List (RWOp ℕ)) (q : ℕ) (h : ∃ v, RWOp.write v ∈ ops) :
    ∃ v, RWOp.write v ∈ ops ∧ (register ℕ 0).runOps q ops = v := by
  induction ops generalizing q with
  | nil => simp at h
  | cons o ops ih =>
    by_cases hw : ∃ v, RWOp.write v ∈ ops
    · obtain ⟨v, hv, he⟩ := ih (((register ℕ 0).δ q o).1) hw
      exact ⟨v, by simp [hv], by rw [ObjSpec.runOps_cons]; exact he⟩
    · obtain ⟨v, hv⟩ := h
      rcases List.mem_cons.1 hv with rfl | hv
      · refine ⟨v, by simp, ?_⟩
        rw [ObjSpec.runOps_cons, register_write, runOps_reads]
        intro o' ho'
        cases o' with
        | read => rfl
        | write u => exact absurd ⟨u, ho'⟩ hw
      · exact absurd ⟨v, hv⟩ hw

/-- The history is not linearizable: `write(1)` returns before the read is invoked, yet the read
returns the initial value `0`, while every write writes `1` or `2`. -/
lemma hist_not_linearizable : ¬ ∃ L, IsLinearization hist L := by
  rintro ⟨L, hL⟩
  have hc : Completed hist (Node.rd, 0) := by simp [Completed, hist, respsOf]
  obtain ⟨y, hyL, hyx⟩ := List.mem_map.1 (hL.complete _ hc)
  obtain ⟨A', B, hsplit⟩ := List.append_of_mem hyL
  -- `write(1)` precedes the read, so it is linearized before it
  have hpre : Precedes hist (Node.wr 0, 0) (Node.rd, 0) :=
    ⟨[.inv (.wr 0) (.write 1), .inv (.wr 1) (.write 2), .ret (.wr 0) 1],
      [.inv .rd .read, .ret .rd 0], rfl, by simp [Completed, respsOf], by simp [Invoked, opsOf]⟩
  have hsub := hL.realtime _ _ hpre (by rw [← hyx]; exact List.mem_map_of_mem hyL)
  have hnd := hL.nodup
  rw [hsplit, List.map_append, List.map_cons, hyx] at hsub hnd
  obtain ⟨z, hzA, hz1⟩ := List.mem_map.1 (Cslib.SharedMemory.mem_left_of_sublist_pair hnd hsub)
  -- the state before the read is the value of the last write in `A'`, which is `1` or `2`
  have hops : ∀ x ∈ L, x.2 = .read ∨ x.2 = .write 1 ∨ x.2 = .write 2 := by
    intro x hx
    have h2 : x.2 ∈ opsOf hist x.1.1 := List.mem_of_getElem? (hL.op_eq x hx)
    obtain ⟨ℓ, hℓ, he⟩ := List.mem_filterMap.1 h2
    simp only [hist, List.mem_cons, List.not_mem_nil, or_false] at hℓ
    rcases hℓ with rfl | rfl | rfl | rfl | rfl <;> simp [Label.invOf] at he <;> simp [← he.2]
  have hz2 : z.2 = .write 1 := by
    have := hL.op_eq z (by rw [hsplit]; simp [hzA])
    rw [hz1] at this; simpa [opOf, opsOf, hist] using this.symm
  have hseq := hL.seq
  rw [hsplit, seqOK_append] at hseq
  have hresp := hseq.2.1 0 (by rw [hyx]; rfl)
  have hy2 : y.2 = .read := by
    have h1 := hL.op_eq y hyL
    rw [hyx, show opOf hist (Node.rd, 0) = some .read from rfl] at h1
    exact (Option.some.inj h1).symm
  rw [hy2] at hresp
  obtain ⟨v, hv, hrun⟩ := runOps_eq_write (A'.map Prod.snd) 0
    ⟨1, by rw [← hz2]; exact List.mem_map_of_mem hzA⟩
  obtain ⟨x, hx, hx2⟩ := List.mem_map.1 hv
  have hv0 : v = 0 := hrun ▸ hresp
  subst hv0
  rcases hops x (by rw [hsplit]; simp [hx]) with h | h | h <;> rw [h] at hx2 <;> simp at hx2

/-- **The W2R1 algorithm of §5.2 is not atomic** (contradicting MWA2 / Lemma 5), for `S = 4`,
`t = 1`, `R = 1 < S/t − 2`, `W = 2`, under both readings of line 20 (`markCur`). -/
theorem w2r1_not_linearizable (mc : Bool) : ¬ (protocol mc).Linearizable := by
  intro h
  obtain ⟨C, hC⟩ := reach_hist mc
  exact hist_not_linearizable (h C hist hC)

end Podc.FastMWMR.W2R1
