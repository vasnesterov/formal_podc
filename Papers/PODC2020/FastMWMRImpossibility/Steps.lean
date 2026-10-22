import Papers.PODC2020.FastMWMRImpossibility.Model

/-!
# Building executions of a W1R2 protocol

Single steps and "waves" (a client's requests delivered to a list of servers, a client collecting
a list of replies) of `W1R2Alg.protocol`, stated with a *frame*: a multiset `N` of messages in
transit that are kept for later steps (`N ≤ C.net`). These are the building blocks of the
executions of the impossibility proof.
-/

namespace Podc.FastMWMR

open Cslib.SharedMemory Cslib.AsyncMP

variable {n : ℕ} {W R V Msg Rep LW LR : Type}
variable [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep]
variable (A : W1R2Alg n W R V Msg Rep LW LR) (t : ℕ) (v₀ : V)

/-- Configurations of a W1R2 protocol. -/
abbrev Cfg (n : ℕ) (W R V Msg Rep LW LR : Type) :=
  Config (Node n W R) (Loc n W R V Msg Rep LW LR) (Pkt Msg Rep)

omit [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep] in
/-- Requests `req k i (m s)` of client `c` to the servers `s ∈ L`. -/
def reqs (c : Node n W R) (k i : ℕ) (m : Fin n → Msg) (L : List (Fin n)) :
    Multiset (Node n W R × Node n W R × Pkt Msg Rep) :=
  Multiset.ofList (L.map fun s => (c, Node.srv s, Pkt.req k i (m s)))

/-- Replies `rep k i (r s)` of the servers `s ∈ L` to client `c`. -/
def reps (c : Node n W R) (k i : ℕ) (r : Fin n → Rep) (L : List (Fin n)) :
    Multiset (Node n W R × Node n W R × Pkt Msg Rep) :=
  Multiset.ofList (L.map fun s => (Node.srv s, c, Pkt.rep k i (r s)))

namespace W1R2Alg

/-- A server processes a request. -/
lemma reach_recv_srv {C : Cfg n W R V Msg Rep LW LR} {h : List (Label (Node n W R) (register V v₀))}
    (hR : (A.protocol t v₀).Reach C h) (hc : C.crashed = ∅) {s : Fin n} {c : Node n W R}
    {k i : ℕ} {m : Msg} {log : List (Node n W R × Msg)} (hl : C.loc (.srv s) = .srv log)
    (hm : (c, Node.srv s, Pkt.req k i m) ∈ C.net) :
    ∃ C' : Cfg n W R V Msg Rep LW LR, (A.protocol t v₀).Reach C' h ∧ C'.crashed = ∅ ∧
      C'.loc = Function.update C.loc (.srv s) (.srv (log ++ [(c, m)])) ∧
      C'.net = C.net.erase (c, .srv s, .req k i m) + {(.srv s, c, .rep k i (A.reply s log c m))} := by
  have hs : (A.protocol t v₀).step C (.recv c (.srv s) (.req k i m)) =
      some (C.apply (.srv s) (.srv (log ++ [(c, m)])) {(c, .rep k i (A.reply s log c m))}
        (C.net.erase (c, .srv s, .req k i m)), none) := by
    simp only [Protocol.step, hc, Finset.notMem_empty, hm, not_true_eq_false, or_self,
      ite_false, hl, W1R2Alg.protocol]
    rfl
  have := Protocol.Reach.step hR hs
  simp only [Option.toList_none, List.append_nil] at this
  exact ⟨_, this, hc, rfl, by simp [Config.apply, outMsgs]⟩

/-- A client processes a reply. -/
lemma reach_recv_client {C : Cfg n W R V Msg Rep LW LR}
    {h : List (Label (Node n W R) (register V v₀))}
    (hR : (A.protocol t v₀).Reach C h) (hc : C.crashed = ∅) {p : Node n W R}
    (hp : ∀ s', p ≠ .srv s') {s : Fin n} {k i : ℕ} {r : Rep}
    (hm : (Node.srv s, p, Pkt.rep k i r) ∈ C.net) :
    ∃ C' : Cfg n W R V Msg Rep LW LR, (A.protocol t v₀).Reach C' h ∧ C'.crashed = ∅ ∧
      C'.loc = Function.update C.loc p ((C.loc p).absorb s k i r) ∧
      C'.net = C.net.erase (.srv s, p, .rep k i r) := by
  have hs : (A.protocol t v₀).step C (.recv (.srv s) p (.rep k i r)) =
      some (C.apply p ((C.loc p).absorb s k i r) 0 (C.net.erase (.srv s, p, .rep k i r)), none) := by
    simp only [Protocol.step, hc, Finset.notMem_empty, hm, not_true_eq_false, or_self,
      ite_false]
    cases p with
    | srv s' => exact absurd rfl (hp s')
    | wr w => rfl
    | rd r => rfl
  have := Protocol.Reach.step hR hs
  simp only [Option.toList_none, List.append_nil] at this
  exact ⟨_, this, hc, rfl, by simp [Config.apply, outMsgs]⟩

omit [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep] in
lemma outMsgs_bcast (p : Node n W R) (k i : ℕ) (f : Fin n → Msg) :
    outMsgs p (bcast (W := W) (R := R) (Rep := Rep) k i f) =
      reqs p k i f (List.finRange n) := by
  simp [outMsgs, bcast, reqs, List.map_map, Function.comp_def]

/-- A writer invokes `write(v)`. -/
lemma reach_inv_wr {C : Cfg n W R V Msg Rep LW LR}
    {h : List (Label (Node n W R) (register V v₀))}
    (hR : (A.protocol t v₀).Reach C h) (hc : C.crashed = ∅) {w : W} {st : LW} {k : ℕ} (v : V)
    (hl : C.loc (.wr w) = .wr st k none) :
    ∃ C' : Cfg n W R V Msg Rep LW LR,
      (A.protocol t v₀).Reach C' (h ++ [.inv (.wr w) (.write v)]) ∧ C'.crashed = ∅ ∧
      C'.loc = Function.update C.loc (.wr w) (.wr st (k + 1) (some (v, []))) ∧
      C'.net = C.net + reqs (.wr w) (k + 1) 1 (A.wMsg w st v) (List.finRange n) := by
  have hs : (A.protocol t v₀).step C (.inv (.wr w) (.write v)) =
      some (C.apply (.wr w) (.wr st (k + 1) (some (v, []))) (bcast (k + 1) 1 (A.wMsg w st v))
        C.net, some (.inv (.wr w) (.write v))) := by
    simp only [Protocol.step, hc, Finset.notMem_empty, ite_false, hl, W1R2Alg.protocol]
    rfl
  have := Protocol.Reach.step hR hs
  simp only [Option.toList_some] at this
  exact ⟨_, this, hc, rfl, by simp only [Config.apply, outMsgs_bcast]⟩

/-- A reader invokes `read()`. -/
lemma reach_inv_rd {C : Cfg n W R V Msg Rep LW LR}
    {h : List (Label (Node n W R) (register V v₀))}
    (hR : (A.protocol t v₀).Reach C h) (hc : C.crashed = ∅) {r : R} {st : LR} {k : ℕ}
    (hl : C.loc (.rd r) = .rd st k .idle) :
    ∃ C' : Cfg n W R V Msg Rep LW LR,
      (A.protocol t v₀).Reach C' (h ++ [.inv (.rd r) .read]) ∧ C'.crashed = ∅ ∧
      C'.loc = Function.update C.loc (.rd r) (.rd st (k + 1) (.one [])) ∧
      C'.net = C.net + reqs (.rd r) (k + 1) 1 (A.rMsg1 r st) (List.finRange n) := by
  have hs : (A.protocol t v₀).step C (.inv (.rd r) .read) =
      some (C.apply (.rd r) (.rd st (k + 1) (.one [])) (bcast (k + 1) 1 (A.rMsg1 r st))
        C.net, some (.inv (.rd r) .read)) := by
    simp only [Protocol.step, hc, Finset.notMem_empty, ite_false, hl, W1R2Alg.protocol]
    rfl
  have := Protocol.Reach.step hR hs
  simp only [Option.toList_some] at this
  exact ⟨_, this, hc, rfl, by simp only [Config.apply, outMsgs_bcast]⟩

/-- A writer with enough replies returns. -/
lemma reach_end_wr {C : Cfg n W R V Msg Rep LW LR}
    {h : List (Label (Node n W R) (register V v₀))}
    (hR : (A.protocol t v₀).Reach C h) (hc : C.crashed = ∅) {w : W} {st : LW} {k : ℕ} {v : V}
    {acks : View n Rep} (hl : C.loc (.wr w) = .wr st k (some (v, acks)))
    (hq : n ≤ acks.length + t) :
    ∃ C' : Cfg n W R V Msg Rep LW LR,
      (A.protocol t v₀).Reach C' (h ++ [.ret (.wr w) v]) ∧ C'.crashed = ∅ ∧
      C'.loc = Function.update C.loc (.wr w) (.wr (A.wEnd w st v acks) k none) ∧
      C'.net = C.net := by
  have hs : (A.protocol t v₀).step C (.internal (.wr w) ()) =
      some (C.apply (.wr w) (.wr (A.wEnd w st v acks) k none) 0 C.net,
        some (.ret (.wr w) v)) := by
    simp only [Protocol.step, hc, Finset.notMem_empty, ite_false, hl, W1R2Alg.protocol, hq,
      ite_true]
    rfl
  have := Protocol.Reach.step hR hs
  simp only [Option.toList_some] at this
  exact ⟨_, this, hc, rfl, by simp [Config.apply, outMsgs]⟩

/-- A reader with enough first-round replies starts its second round-trip. -/
lemma reach_mid_rd {C : Cfg n W R V Msg Rep LW LR}
    {h : List (Label (Node n W R) (register V v₀))}
    (hR : (A.protocol t v₀).Reach C h) (hc : C.crashed = ∅) {r : R} {st : LR} {k : ℕ}
    {acks : View n Rep} (hl : C.loc (.rd r) = .rd st k (.one acks))
    (hq : n ≤ acks.length + t) :
    ∃ C' : Cfg n W R V Msg Rep LW LR,
      (A.protocol t v₀).Reach C' h ∧ C'.crashed = ∅ ∧
      C'.loc = Function.update C.loc (.rd r) (.rd st k (.two acks [])) ∧
      C'.net = C.net + reqs (.rd r) k 2 (A.rMsg2 r st acks) (List.finRange n) := by
  have hs : (A.protocol t v₀).step C (.internal (.rd r) ()) =
      some (C.apply (.rd r) (.rd st k (.two acks [])) (bcast k 2 (A.rMsg2 r st acks)) C.net,
        none) := by
    simp only [Protocol.step, hc, Finset.notMem_empty, ite_false, hl, W1R2Alg.protocol, hq,
      ite_true]
    rfl
  have := Protocol.Reach.step hR hs
  simp only [Option.toList_none, List.append_nil] at this
  exact ⟨_, this, hc, rfl, by simp only [Config.apply, outMsgs_bcast]⟩

/-- A reader with enough second-round replies returns. -/
lemma reach_end_rd {C : Cfg n W R V Msg Rep LW LR}
    {h : List (Label (Node n W R) (register V v₀))}
    (hR : (A.protocol t v₀).Reach C h) (hc : C.crashed = ∅) {r : R} {st : LR} {k : ℕ}
    {V₁ acks : View n Rep} (hl : C.loc (.rd r) = .rd st k (.two V₁ acks))
    (hq : n ≤ acks.length + t) :
    ∃ C' : Cfg n W R V Msg Rep LW LR,
      (A.protocol t v₀).Reach C' (h ++ [.ret (.rd r) (A.rEnd r st V₁ acks).1]) ∧
      C'.crashed = ∅ ∧
      C'.loc = Function.update C.loc (.rd r) (.rd (A.rEnd r st V₁ acks).2 k .idle) ∧
      C'.net = C.net := by
  have hs : (A.protocol t v₀).step C (.internal (.rd r) ()) =
      some (C.apply (.rd r) (.rd (A.rEnd r st V₁ acks).2 k .idle) 0 C.net,
        some (.ret (.rd r) (A.rEnd r st V₁ acks).1)) := by
    simp only [Protocol.step, hc, Finset.notMem_empty, ite_false, hl, W1R2Alg.protocol, hq,
      ite_true]
    rfl
  have := Protocol.Reach.step hR hs
  simp only [Option.toList_some] at this
  exact ⟨_, this, hc, rfl, by simp [Config.apply, outMsgs]⟩

/-- A *wave*: the requests `req k i (m s)` of client `c` are delivered to the servers of `L`, in
order. The replies are added to the network; the messages of the frame `N` stay in transit. -/
lemma reach_wave {C : Cfg n W R V Msg Rep LW LR} {h : List (Label (Node n W R) (register V v₀))}
    (hR : (A.protocol t v₀).Reach C h) (hc : C.crashed = ∅) (c : Node n W R) (k i : ℕ)
    (m : Fin n → Msg) (lg : Fin n → List (Node n W R × Msg)) (L : List (Fin n)) (hL : L.Nodup)
    (hlog : ∀ s ∈ L, C.loc (.srv s) = .srv (lg s)) (N : Multiset (Node n W R × Node n W R × Pkt Msg Rep))
    (hN : reqs c k i m L + N ≤ C.net) :
    ∃ C' : Cfg n W R V Msg Rep LW LR, (A.protocol t v₀).Reach C' h ∧ C'.crashed = ∅ ∧
      (∀ s ∈ L, C'.loc (.srv s) = .srv (lg s ++ [(c, m s)])) ∧
      (∀ p, (∀ s ∈ L, p ≠ .srv s) → C'.loc p = C.loc p) ∧
      reps c k i (fun s => A.reply s (lg s) c (m s)) L + N ≤ C'.net := by
  induction L generalizing C N with
  | nil => exact ⟨C, hR, hc, by simp, by simp, by simpa [reqs, reps] using hN⟩
  | cons s L ih =>
    rw [List.nodup_cons] at hL
    have hN' : (c, Node.srv s, Pkt.req k i (m s)) ::ₘ (reqs c k i m L + N) ≤ C.net := by
      rw [← Multiset.cons_add]; exact hN
    obtain ⟨C₁, hR₁, hc₁, hl₁, hn₁⟩ := A.reach_recv_srv t v₀ hR hc (hlog s (by simp))
      (Multiset.mem_of_le hN' (Multiset.mem_cons_self _ _))
    have hle : reqs c k i m L + N ≤ C.net.erase (c, Node.srv s, Pkt.req k i (m s)) := by
      simpa using Multiset.erase_le_erase (c, Node.srv s, Pkt.req k i (m s)) hN'
    obtain ⟨C', hR', hc', hl', ho', hn'⟩ := ih hR₁ hc₁ hL.2
      (fun s' hs' => by
        rw [hl₁, Function.update_of_ne (by
          intro he; cases he; exact hL.1 hs')]
        exact hlog s' (by simp [hs']))
      (N + {(Node.srv s, c, Pkt.rep k i (A.reply s (lg s) c (m s)))})
      (by rw [hn₁, ← add_assoc]; exact add_le_add hle le_rfl)
    refine ⟨C', hR', hc', ?_, ?_, ?_⟩
    · intro s' hs'
      rcases List.mem_cons.1 hs' with rfl | hs'
      · rw [ho' _ (fun s'' hs'' he => by cases he; exact hL.1 hs''), hl₁]; simp
      · exact hl' s' hs'
    · intro p hp
      rw [ho' p (fun s' hs' => hp s' (by simp [hs'])), hl₁,
        Function.update_of_ne (hp s (by simp))]
    · convert hn' using 1
      rw [show reps c k i (fun s => A.reply s (lg s) c (m s)) (s :: L) =
        (Node.srv s, c, Pkt.rep k i (A.reply s (lg s) c (m s))) ::ₘ
          reps c k i (fun s => A.reply s (lg s) c (m s)) L from rfl,
        add_comm N, Multiset.singleton_add, Multiset.add_cons, Multiset.cons_add]

/-- A client collects the replies `rep k i (rr s)` of the servers of `L`, in order. -/
lemma reach_collect {C : Cfg n W R V Msg Rep LW LR}
    {h : List (Label (Node n W R) (register V v₀))}
    (hR : (A.protocol t v₀).Reach C h) (hc : C.crashed = ∅) (p : Node n W R)
    (hp : ∀ s', p ≠ .srv s') (k i : ℕ) (rr : Fin n → Rep) (L : List (Fin n))
    (N : Multiset (Node n W R × Node n W R × Pkt Msg Rep)) (hN : reps p k i rr L + N ≤ C.net) :
    ∃ C' : Cfg n W R V Msg Rep LW LR, (A.protocol t v₀).Reach C' h ∧ C'.crashed = ∅ ∧
      C'.loc p = L.foldl (fun l s => l.absorb s k i (rr s)) (C.loc p) ∧
      (∀ q, q ≠ p → C'.loc q = C.loc q) ∧ N ≤ C'.net := by
  induction L generalizing C with
  | nil => exact ⟨C, hR, hc, rfl, fun _ _ => rfl, by simpa [reps] using hN⟩
  | cons s L ih =>
    have hN' : (Node.srv s, p, Pkt.rep k i (rr s)) ::ₘ (reps p k i rr L + N) ≤ C.net := by
      rw [← Multiset.cons_add]; exact hN
    obtain ⟨C₁, hR₁, hc₁, hl₁, hn₁⟩ := A.reach_recv_client t v₀ hR hc hp
      (Multiset.mem_of_le hN' (Multiset.mem_cons_self _ _))
    obtain ⟨C', hR', hc', hl', ho', hn'⟩ := ih hR₁ hc₁ (by
      rw [hn₁]; simpa using Multiset.erase_le_erase (Node.srv s, p, Pkt.rep k i (rr s)) hN')
    refine ⟨C', hR', hc', ?_, ?_, hn'⟩
    · rw [hl', hl₁]; simp
    · intro q hq; rw [ho' q hq, hl₁, Function.update_of_ne hq]

omit [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep] in
@[simp] lemma absorb_wr (st : LW) (k : ℕ) (v : V) (acks : View n Rep) (s : Fin n) (r : Rep) :
    (Loc.wr (W := W) (R := R) (Msg := Msg) (LR := LR) st k (some (v, acks))).absorb s k 1 r =
      .wr st k (some (v, acks ++ [(s, r)])) := by simp [Loc.absorb]

omit [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep] in
@[simp] lemma absorb_one (st : LR) (k : ℕ) (acks : View n Rep) (s : Fin n) (r : Rep) :
    (Loc.rd (W := W) (R := R) (V := V) (Msg := Msg) (LW := LW) st k (.one acks)).absorb s k 1 r =
      .rd st k (.one (acks ++ [(s, r)])) := by simp [Loc.absorb]

omit [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep] in
@[simp] lemma absorb_two (st : LR) (k : ℕ) (V₁ acks : View n Rep) (s : Fin n) (r : Rep) :
    (Loc.rd (W := W) (R := R) (V := V) (Msg := Msg) (LW := LW) st k (.two V₁ acks)).absorb s k 2 r =
      .rd st k (.two V₁ (acks ++ [(s, r)])) := by simp [Loc.absorb]

omit [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep] in
lemma foldl_absorb_wr (L : List (Fin n)) (st : LW) (k : ℕ) (v : V) (acks : View n Rep)
    (rr : Fin n → Rep) :
    L.foldl (fun l s => l.absorb s k 1 (rr s))
      (Loc.wr (W := W) (R := R) (Msg := Msg) (LR := LR) st k (some (v, acks))) =
      .wr st k (some (v, acks ++ L.map fun s => (s, rr s))) := by
  induction L generalizing acks with
  | nil => simp
  | cons s L ih => simp only [List.foldl_cons, absorb_wr, ih]; simp

omit [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep] in
lemma foldl_absorb_one (L : List (Fin n)) (st : LR) (k : ℕ) (acks : View n Rep)
    (rr : Fin n → Rep) :
    L.foldl (fun l s => l.absorb s k 1 (rr s))
      (Loc.rd (W := W) (R := R) (V := V) (Msg := Msg) (LW := LW) st k (.one acks)) =
      .rd st k (.one (acks ++ L.map fun s => (s, rr s))) := by
  induction L generalizing acks with
  | nil => simp
  | cons s L ih => simp only [List.foldl_cons, absorb_one, ih]; simp

omit [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep] in
lemma foldl_absorb_two (L : List (Fin n)) (st : LR) (k : ℕ) (V₁ acks : View n Rep)
    (rr : Fin n → Rep) :
    L.foldl (fun l s => l.absorb s k 2 (rr s))
      (Loc.rd (W := W) (R := R) (V := V) (Msg := Msg) (LW := LW) st k (.two V₁ acks)) =
      .rd st k (.two V₁ (acks ++ L.map fun s => (s, rr s))) := by
  induction L generalizing acks with
  | nil => simp
  | cons s L ih => simp only [List.foldl_cons, absorb_two, ih]; simp

end W1R2Alg

end Podc.FastMWMR
