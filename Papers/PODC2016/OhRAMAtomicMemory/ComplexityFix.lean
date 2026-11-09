import Papers.PODC2016.OhRAMAtomicMemory.Complexity

/-!
# The repaired read message complexity

With the test of line 53 nested in the `if` of line 51 (`Vr.fixAck = true`), a server sends at
most one `readAck` per read, and every read has at most `|S| + |S|·(|S| + [fast]) + |S|`
messages: `|S|² + 2|S|` (OhSam, OhMam) and `|S|² + 3|S|` (OhSam', OhMam'), as claimed in
Table 1 (`readMsgBound_fix`).
-/

set_option linter.unusedSectionVars false

namespace Podc.OhRAM.Cplx

open Cslib.SharedMemory Cslib.AsyncMP

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V]

/-- `readRequest`s of the `k`-th read of `r`. -/
def ReqP (r : R) (k : ℕ) (x : Node W R S × Node W R S × Msg R T V) : Bool :=
  decide (x.1 = .rd r ∧ x.2.2 = .readRequest k)

/-- `readRelay`s for the `k`-th read of `r`. -/
def RelP (r : R) (k : ℕ) (x : Node W R S × Node W R S × Msg R T V) : Bool :=
  match x.2.2 with
  | .readRelay _ _ r' k' => decide (r' = r ∧ k' = k)
  | _ => false

/-- `readAck`s for the `k`-th read of `r`. -/
def AckP (r : R) (k : ℕ) (x : Node W R S × Node W R S × Msg R T V) : Bool :=
  match x.2.1, x.2.2 with
  | .rd r', .readAck _ _ k' => decide (r' = r ∧ k' = k)
  | _, _ => false

lemma isReadMsg_imp (r : R) (k : ℕ) (x : Node W R S × Node W R S × Msg R T V)
    (h : IsReadMsg r k x = true) : ReqP r k x = true ∨ RelP r k x = true ∨ AckP r k x = true := by
  obtain ⟨a, b, m⟩ := x
  cases m <;> cases a <;> cases b <;> simp_all [IsReadMsg, ReqP, RelP, AckP]

lemma countP_le_three {α : Type} (s : Multiset α) (f g₁ g₂ g₃ : α → Bool)
    (h : ∀ x, f x = true → g₁ x = true ∨ g₂ x = true ∨ g₃ x = true) :
    s.countP (fun x => f x) ≤ s.countP (fun x => g₁ x) + s.countP (fun x => g₂ x) +
      s.countP (fun x => g₃ x) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.countP_cons]
    have := h a
    split_ifs <;> simp_all <;> omega

/-- Classification of the steps of a protocol on `Cslib.AsyncMP` without internal actions. -/
lemma step_cases' {P L M : Type} {A : ObjSpec} [DecidableEq P] [DecidableEq M] {Pr : Protocol P A L M Empty}
    {C C' : Config P L M} {st : Step P A M Empty} {ℓ : Option (Label P A)}
    (h : Pr.step C st = some (C', ℓ)) :
    (C'.loc = C.loc ∧ C'.sent = C.sent ∧ C'.net ≤ C.net) ∨
    (∃ p o x, Pr.invoke p o (C.loc p) = some x ∧ C' = C.apply p x.1 x.2 C.net) ∨
    (∃ src dst m x, (src, dst, m) ∈ C.net ∧ Pr.receive dst src m (C.loc dst) = some x ∧
      C' = C.apply dst x.1 x.2.1 (C.net.erase (src, dst, m))) := by
  cases st with
  | inv p o =>
    simp only [Protocol.step] at h
    split_ifs at h
    obtain ⟨x, hx, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he
    exact Or.inr (Or.inl ⟨p, o, x, hx, he.1.symm⟩)
  | internal p a => exact a.elim
  | recv src dst m =>
    simp only [Protocol.step] at h
    split_ifs at h with hc
    push Not at hc
    obtain ⟨x, hx, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he
    exact Or.inr (Or.inr ⟨src, dst, m, x, hc.2, hx, he.1.symm⟩)
  | drop src dst m =>
    simp only [Protocol.step] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl, Multiset.erase_le _ _⟩
  | crash p =>
    simp only [Protocol.step] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl, le_rfl⟩
  | skip =>
    simp only [Protocol.step, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl, le_rfl⟩

lemma countP_outMsgs {P M : Type} (p : P) (out : Multiset (P × M)) (g : P × P × M → Bool) :
    (outMsgs p out).countP (fun x => g x) = out.countP (fun y => g (p, y.1, y.2)) := by
  rw [outMsgs, Multiset.countP_map]
  simp [Multiset.countP_eq_card_filter]

/-- Server state `l` has (or would have) sent its `readAck` for the `k`-th read of `r`. -/
def Memb (l : SLoc W R S T V) (r : R) (k : ℕ) : Prop :=
  k < l.ops r ∨ (l.ops r = k ∧ maj S ≤ l.relays r)

instance (l : SLoc W R S T V) (r : R) (k : ℕ) : Decidable (Memb l r k) := by
  unfold Memb; infer_instance

lemma sRelay_memb (Vr : Variant) (sj : S) (t : T) (v : V) (r : R) (k : ℕ) (l : SLoc W R S T V)
    (r' : R) (k' : ℕ) (h : Memb l r' k') : Memb (sRelay Vr sj t v r k l).1 r' k' := by
  unfold Memb at *
  simp only [sRelay]
  by_cases hr : r' = r
  · subst hr
    split_ifs <;> simp_all [Function.update] <;> omega
  · split_ifs <;> simp_all [Function.update]

lemma sRelay_ack (Vr : Variant) (hfix : Vr.fixAck = true) (sj : S) (t : T) (v : V) (r : R)
    (k : ℕ) (l : SLoc W R S T V) (r' : R) (k' : ℕ) (x : Node W R S) :
    (sRelay Vr sj t v r k l).2.countP (fun y => AckP r' k' (x, y.1, y.2)) ≤
      if Memb (sRelay Vr sj t v r k l).1 r' k' ∧ ¬ Memb l r' k' then 1 else 0 := by
  have hs : ∀ (a : Node W R S × Msg R T V) (g : Node W R S × Msg R T V → Bool),
      ({a} : Multiset _).countP (fun y => g y) = if g a then 1 else 0 := by
    intro a g; rw [← Multiset.cons_zero, Multiset.countP_cons]; simp
  unfold Memb
  simp only [sRelay, hfix]
  by_cases hrk : r' = r ∧ k' = k
  · obtain ⟨rfl, rfl⟩ := hrk
    split_ifs <;> simp_all [AckP, Function.update] <;> omega
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    split_ifs <;> first | rfl | (rw [hs]; simp only [AckP]; split_ifs <;> simp_all)

/-- The message is a `readRequest`, `readRelay` or `readAck`. -/
def ReadKind : Msg R T V → Bool
  | .readRequest _ => true
  | .readRelay .. => true
  | .readAck .. => true
  | _ => false

lemma countP_zero_of_not_readKind {p : Node W R S} {out : Multiset (Node W R S × Msg R T V)}
    (h : ∀ y ∈ out, ReadKind y.2 = false) (r : R) (k : ℕ) :
    (outMsgs p out).countP (fun x => ReqP r k x) = 0 ∧
    (outMsgs p out).countP (fun x => RelP r k x) = 0 ∧
    (outMsgs p out).countP (fun x => AckP r k x) = 0 := by
  simp only [countP_outMsgs, Multiset.countP_eq_zero]
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩ <;>
  · have := h y hy
    obtain ⟨d, m⟩ := y
    cases m <;> cases d <;> simp_all [ReadKind, ReqP, RelP, AckP]

lemma countP_bcast (p : Node W R S) (m : Msg R T V) (g : Node W R S × Node W R S × Msg R T V → Bool)
    (b : Bool) (hg : ∀ s, g (p, .sv s, m) = b) :
    (outMsgs p (bcast (S := S) m)).countP (fun x => g x) = if b then Fintype.card S else 0 := by
  rw [countP_outMsgs, bcast, Multiset.countP_map]
  simp only [hg]
  cases b <;> simp [Finset.card_univ]

lemma countP_erase_of_mem {α : Type} [DecidableEq α] (s : Multiset α) (a : α) (g : α → Bool)
    (ha : a ∈ s) : (s.erase a).countP (fun x => g x) + (if g a then 1 else 0) =
      s.countP (fun x => g x) := by
  conv_rhs => rw [← Multiset.cons_erase ha]
  rw [Multiset.countP_cons]

lemma countP_const {α : Type} (s : Multiset α) (g : α → Bool) (b : Bool) (h : ∀ y ∈ s, g y = b) :
    s.countP (fun x => g x) = if b then Multiset.card s else 0 := by
  cases b
  · simp only [Bool.false_eq_true, ite_false, Multiset.countP_eq_zero]; intro y hy; simp [h y hy]
  · simp only [ite_true, Multiset.countP_eq_card]; intro y hy; simp [h y hy]

/-- Extra relays sent to the reader by a server (revised protocol). -/
def fw (Vr : Variant) : ℕ := if Vr.fast then 1 else 0

/-- The servers that have sent (or would have sent) their `readAck` for the `k`-th read of `r`. -/
def acked (L : Node W R S → Loc W R S T V) (r : R) (k : ℕ) : Finset S :=
  Finset.univ.filter (fun s => Memb (L (.sv s)).s r k)

/-- Counting invariant for the read messages. -/
structure CInv (Vr : Variant) (C : Config (Node W R S) (Loc W R S T V) (Msg R T V)) : Prop where
  req : ∀ r k, C.sent.countP (fun x => ReqP r k x) ≤
    if k ≤ (C.loc (.rd r)).r.op then Fintype.card S else 0
  rel : ∀ r k, C.sent.countP (fun x => RelP r k x) +
      (Fintype.card S + fw Vr) * C.net.countP (fun x => ReqP r k x) ≤
    (Fintype.card S + fw Vr) * C.sent.countP (fun x => ReqP r k x)
  ack : ∀ r k, C.sent.countP (fun x => AckP r k x) ≤ (acked C.loc r k).card

lemma acked_congr {L L' : Node W R S → Loc W R S T V}
    (h : ∀ s, (L' (.sv s)).s.ops = (L (.sv s)).s.ops ∧ (L' (.sv s)).s.relays = (L (.sv s)).s.relays)
    (r : R) (k : ℕ) : acked L' r k = acked L r k := by
  ext s; simp only [acked, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold Memb; rw [(h s).1, (h s).2]

lemma countP_zero_of_not_readKind' {E : Multiset (Node W R S × Node W R S × Msg R T V)}
    (h : ∀ x ∈ E, ReadKind x.2.2 = false) (r : R) (k : ℕ) :
    E.countP (fun x => ReqP r k x) = 0 ∧ E.countP (fun x => RelP r k x) = 0 ∧
    E.countP (fun x => AckP r k x) = 0 := by
  simp only [Multiset.countP_eq_zero]
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩ <;>
  · have := h y hy
    obtain ⟨a, d, m⟩ := y
    cases m <;> cases d <;> simp_all [ReadKind, ReqP, RelP, AckP]

lemma outMsgs_noRead {p : Node W R S} {out : Multiset (Node W R S × Msg R T V)}
    (h : ∀ y ∈ out, ReadKind y.2 = false) : ∀ x ∈ outMsgs p out, ReadKind x.2.2 = false := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
  exact h y hy

/-- Steps that send no read message and change no counter preserve `CInv`. -/
lemma CInv.quiet {Vr : Variant} {C C' : Config (Node W R S) (Loc W R S T V) (Msg R T V)}
    (hI : CInv Vr C) (hop : ∀ r, (C'.loc (.rd r)).r.op = (C.loc (.rd r)).r.op)
    (hsv : ∀ s, (C'.loc (.sv s)).s.ops = (C.loc (.sv s)).s.ops ∧
      (C'.loc (.sv s)).s.relays = (C.loc (.sv s)).s.relays)
    (E : Multiset (Node W R S × Node W R S × Msg R T V))
    (hE : ∀ x ∈ E, ReadKind x.2.2 = false) (hsent : C'.sent = C.sent + E)
    (hnet : C'.net ≤ C.net + E) : CInv Vr C' := by
  have hz := countP_zero_of_not_readKind' hE
  refine ⟨fun r k => ?_, fun r k => ?_, fun r k => ?_⟩
  · rw [hsent, Multiset.countP_add, (hz r k).1, hop]; simpa using hI.req r k
  · have h1 := Multiset.countP_le_of_le (fun x => ReqP r k x = true) hnet
    rw [Multiset.countP_add, (hz r k).1] at h1
    rw [hsent, Multiset.countP_add, Multiset.countP_add, (hz r k).1, (hz r k).2.1]
    have := hI.rel r k
    have := Nat.mul_le_mul_left (Fintype.card S + fw Vr) h1
    simp only [add_zero] at *
    omega
  · rw [hsent, Multiset.countP_add, (hz r k).2.2, acked_congr hsv]; simpa using hI.ack r k

lemma acked_update (L : Node W R S → Loc W R S T V) (sx : S) (l' : Loc W R S T V)
    (hmono : ∀ r k, Memb (L (.sv sx)).s r k → Memb l'.s r k) (r : R) (k : ℕ) :
    (acked L r k).card + (if Memb l'.s r k ∧ ¬ Memb (L (.sv sx)).s r k then 1 else 0) ≤
      (acked (Function.update L (.sv sx) l') r k).card := by
  have hsub : acked L r k ⊆ acked (Function.update L (.sv sx) l') r k := by
    intro s hs
    simp only [acked, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    by_cases hs' : s = sx
    · subst hs'; simpa using hmono r k hs
    · rwa [Function.update_of_ne (by simpa using hs')]
  split_ifs with hc
  · have hnot : sx ∉ acked L r k := by simp [acked, hc.2]
    have hin : sx ∈ acked (Function.update L (.sv sx) l') r k := by simp [acked, hc.1]
    have := Finset.card_le_card (Finset.insert_subset hin hsub)
    rw [Finset.card_insert_of_notMem hnot] at this
    exact this
  · simpa using Finset.card_le_card hsub

lemma wInvoke_noRead {Vr : Variant} {next : W → T → T} {w : W} {val : V} {l : WLoc S T V} {y}
    (h : wInvoke (R := R) Vr next w val l = some y) : ∀ z ∈ y.2, ReadKind z.2 = false := by
  unfold wInvoke at h
  split at h
  · split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
      intro z hz <;> obtain ⟨s, -, rfl⟩ := Multiset.mem_map.1 hz <;> rfl
  · simp at h

lemma wWait_noRead (next : W → T → T) (w : W) (l : WLoc S T V) :
    ∀ z ∈ (wWait (R := R) next w l).2.1, ReadKind z.2 = false := by
  unfold wWait
  split_ifs
  · split <;> simp only [Multiset.notMem_zero, false_imp_iff, imp_true_iff]
    intro z hz; obtain ⟨s, -, rfl⟩ := Multiset.mem_map.1 hz; rfl
  · simp

lemma sRelay_out (Vr : Variant) (sj : S) (t : T) (v : V) (r : R) (k : ℕ) (l : SLoc W R S T V) :
    ∀ z ∈ (sRelay Vr sj t v r k l).2, ∃ t' v', z.2 = Msg.readAck t' v' k := by
  intro z hz
  simp only [sRelay] at hz
  split_ifs at hz <;> simp_all

lemma rWait_rRecord_op (Vr : Variant) (v₀ : V) (s : S) (m : Msg R T V) (l : RLoc S T V) :
    (rWait Vr v₀ (rRecord Vr s m l)).1.op = l.op := by
  have h1 : (rRecord Vr s m l).op = l.op := by
    unfold rRecord; split <;> (try split_ifs) <;> rfl
  rw [← h1]
  unfold rWait
  split_ifs <;> (try split) <;> rfl

lemma sRecv_cases (Vr : Variant) (src : Node W R S) (m : Msg R T V) (l : SLoc W R S T V) :
    (∃ r k, src = .rd r ∧ m = .readRequest k ∧ (sRecv Vr src m l).1 = l ∧
      (sRecv Vr src m l).2 = bcast (.readRelay l.tag l.val r k) +
        if Vr.fast then {(Node.rd r, Msg.readRelay l.tag l.val r k)} else 0) ∨
    (∃ sj t v r k, src = .sv sj ∧ m = .readRelay t v r k ∧
      sRecv Vr src m l = sRelay Vr sj t v r k l) ∨
    ((sRecv Vr src m l).1.ops = l.ops ∧ (sRecv Vr src m l).1.relays = l.relays ∧
      ∀ z ∈ (sRecv Vr src m l).2, ReadKind z.2 = false) := by
  unfold sRecv
  split
  · exact Or.inl ⟨_, _, rfl, rfl, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨_, _, _, _, _, rfl, rfl, rfl⟩)
  · right; right
    simp only [sWrite]
    split_ifs <;> simp [ReadKind]
  · right; right; simp [ReadKind]
  · right; right; simp

/-- `CInv` is preserved by every step when line 53 is repaired. -/
lemma CInv.step {Vr : Variant} (hfix : Vr.fixAck = true) {next : W → T → T} {v₀ : V}
    {C C' : Config (Node W R S) (Loc W R S T V) (Msg R T V)}
    {st : Step (Node W R S) (register V v₀) (Msg R T V) Empty} {ℓ}
    (hI : CInv Vr C) (h : (proto Vr next v₀).step C st = some (C', ℓ)) : CInv Vr C' := by
  rcases step_cases' h with ⟨hl, hs, hn⟩ | ⟨p, o, x, hx, rfl⟩ | ⟨src, dst, m, x, hmem, hx, rfl⟩
  · exact hI.quiet (by simp [hl]) (by simp [hl]) 0 (by simp) (by simp [hs]) (by simpa using hn)
  · cases p with
    | wr w =>
      cases o with
      | read => simp [proto] at hx
      | write val =>
        simp only [proto, Option.map_eq_some_iff] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact hI.quiet (fun r => by simp [Config.apply]) (fun s => by simp [Config.apply])
          (outMsgs (.wr w) y.2) (outMsgs_noRead (wInvoke_noRead hy)) rfl le_rfl
    | rd r0 =>
      cases o with
      | write v => simp [proto] at hx
      | read =>
        simp only [proto, Option.map_eq_some_iff] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        simp only [rInvoke] at hy
        split_ifs at hy with hp
        simp only [Option.some.injEq] at hy; subst hy
        clear h
        set op := (C.loc (Node.rd r0)).r.op with hop
        have hq : ∀ r k, (outMsgs (Node.rd r0 : Node W R S) (bcast (S := S)
            (Msg.readRequest (op + 1) : Msg R T V))).countP (fun x => ReqP r k x) =
            if r0 = r ∧ op + 1 = k then Fintype.card S else 0 := by
          intro r k
          rw [countP_bcast _ _ _ (decide (r0 = r ∧ op + 1 = k))]
          · simp
          · intro s; simp [ReqP]
        have hz : ∀ r k, (outMsgs (Node.rd r0 : Node W R S) (bcast (S := S)
            (Msg.readRequest (op + 1) : Msg R T V))).countP (fun x => RelP r k x) = 0 ∧
            (outMsgs (Node.rd r0 : Node W R S) (bcast (S := S)
            (Msg.readRequest (op + 1) : Msg R T V))).countP (fun x => AckP r k x) = 0 := by
          intro r k
          refine ⟨?_, ?_⟩
          · rw [countP_bcast _ _ _ false (fun s => by simp [RelP])]; simp
          · rw [countP_bcast _ _ _ false (fun s => by simp [AckP])]; simp
        refine ⟨fun r k => ?_, fun r k => ?_, fun r k => ?_⟩
        · simp only [Config.apply, Multiset.countP_add, hq]
          have := hI.req r k
          by_cases hr : r = r0
          · subst hr
            simp only [Function.update_self, true_and]
            split_ifs at this ⊢ <;> omega
          · have hne : (Node.rd r : Node W R S) ≠ Node.rd r0 := by simpa using hr
            simp only [Function.update_of_ne hne, Ne.symm hr, false_and, ite_false, add_zero]
            exact this
        · simp only [Config.apply, Multiset.countP_add, hq, (hz r k).1]
          have := hI.rel r k
          split_ifs <;> simp only [add_zero, Nat.mul_add] <;> omega
        · simp only [Config.apply, Multiset.countP_add, (hz r k).2, add_zero]
          rw [acked_congr (L := C.loc) (fun s => by simp [Function.update_of_ne])]
          exact hI.ack r k
    | sv s => cases o <;> simp [proto] at hx
  · have hle : C.net.erase (src, dst, m) ≤ C.net := Multiset.erase_le _ _
    cases dst with
    | wr w =>
      cases src with
      | sv s0 =>
        simp only [proto, Option.some.injEq] at hx; subst hx
        exact hI.quiet (fun r => by simp [Config.apply]) (fun s => by simp [Config.apply])
          _ (outMsgs_noRead (wWait_noRead _ _ _)) rfl (by simpa [Config.apply] using hle)
      | wr _ =>
        simp only [proto, Option.some.injEq] at hx; subst hx
        exact hI.quiet (fun r => by simp [Config.apply]) (fun s => by simp [Config.apply])
          0 (by simp) (by simp [Config.apply, outMsgs]) (by simpa [Config.apply, outMsgs] using hle)
      | rd _ =>
        simp only [proto, Option.some.injEq] at hx; subst hx
        exact hI.quiet (fun r => by simp [Config.apply]) (fun s => by simp [Config.apply])
          0 (by simp) (by simp [Config.apply, outMsgs]) (by simpa [Config.apply, outMsgs] using hle)
    | rd r0 =>
      cases src with
      | sv s0 =>
        simp only [proto, Option.some.injEq] at hx; subst hx
        refine hI.quiet (fun r => ?_) (fun s => by simp [Config.apply])
          0 (by simp) (by simp [Config.apply, outMsgs]) (by simpa [Config.apply, outMsgs] using hle)
        by_cases hr : r = r0
        · subst hr; simp [Config.apply, rWait_rRecord_op]
        · have hne : (Node.rd r : Node W R S) ≠ Node.rd r0 := by simpa using hr
          simp [Config.apply, Function.update_of_ne hne]
      | wr _ =>
        simp only [proto, Option.some.injEq] at hx; subst hx
        exact hI.quiet (fun r => by simp [Config.apply]) (fun s => by simp [Config.apply])
          0 (by simp) (by simp [Config.apply, outMsgs]) (by simpa [Config.apply, outMsgs] using hle)
      | rd _ =>
        simp only [proto, Option.some.injEq] at hx; subst hx
        exact hI.quiet (fun r => by simp [Config.apply]) (fun s => by simp [Config.apply])
          0 (by simp) (by simp [Config.apply, outMsgs]) (by simpa [Config.apply, outMsgs] using hle)
    | sv sx =>
      simp only [proto, Option.some.injEq] at hx; subst hx
      rcases sRecv_cases Vr src m (C.loc (.sv sx)).s with
        ⟨r0, k0, rfl, rfl, h1, h2⟩ | ⟨sj, t, v, r0, k0, rfl, rfl, h1⟩ | ⟨h1, h2, h3⟩
      · have hloc : Function.update C.loc (Node.sv sx)
            { C.loc (Node.sv sx) with
              s := (sRecv Vr (Node.rd r0) (Msg.readRequest k0) (C.loc (Node.sv sx)).s).1 } =
            C.loc := by rw [h1]; simp
        have hmem' : ∀ y ∈ outMsgs (Node.sv sx) (sRecv Vr (Node.rd r0) (Msg.readRequest k0) (C.loc (Node.sv sx)).s).2, y.1 = Node.sv sx ∧
            y.2.2 = .readRelay (C.loc (.sv sx)).s.tag (C.loc (.sv sx)).s.val r0 k0 := by
          intro y hy
          obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
          rw [h2] at hz
          refine ⟨rfl, ?_⟩
          rcases Multiset.mem_add.1 hz with hz | hz
          · obtain ⟨s, -, rfl⟩ := Multiset.mem_map.1 hz; rfl
          · split_ifs at hz
            · rw [Multiset.mem_singleton.1 hz]
            · simp at hz
        have hcard : Multiset.card (outMsgs (Node.sv sx) (sRecv Vr (Node.rd r0) (Msg.readRequest k0) (C.loc (Node.sv sx)).s).2) = Fintype.card S + fw Vr := by
          rw [outMsgs, Multiset.card_map, h2, Multiset.card_add, bcast, Multiset.card_map]
          simp only [fw, Finset.card_val, Finset.card_univ]
          split_ifs <;> simp
        have hq : ∀ r k, (outMsgs (Node.sv sx) (sRecv Vr (Node.rd r0) (Msg.readRequest k0) (C.loc (Node.sv sx)).s).2).countP (fun x => ReqP r k x) = 0 :=
          fun r k => by
            rw [countP_const _ _ false (fun y hy => by
              obtain ⟨h1, h2⟩ := hmem' y hy; simp [ReqP, h1, h2])]; rfl
        have ha : ∀ r k, (outMsgs (Node.sv sx) (sRecv Vr (Node.rd r0) (Msg.readRequest k0) (C.loc (Node.sv sx)).s).2).countP (fun x => AckP r k x) = 0 :=
          fun r k => by
            rw [countP_const _ _ false (fun y hy => by
              obtain ⟨h1, h2⟩ := hmem' y hy
              obtain ⟨a, b, c⟩ := y
              simp only at h1 h2; subst h2
              cases b <;> simp [AckP])]; rfl
        have hl : ∀ r k, (outMsgs (Node.sv sx) (sRecv Vr (Node.rd r0) (Msg.readRequest k0) (C.loc (Node.sv sx)).s).2).countP (fun x => RelP r k x) =
            if r0 = r ∧ k0 = k then Fintype.card S + fw Vr else 0 := fun r k => by
          rw [countP_const _ _ (decide (r0 = r ∧ k0 = k)) (fun y hy => by
            obtain ⟨h1, h2⟩ := hmem' y hy; simp [RelP, h2]), hcard]
          simp
        have he := fun r k => countP_erase_of_mem C.net _ (fun x => ReqP r k x) hmem
        refine ⟨fun r k => ?_, fun r k => ?_, fun r k => ?_⟩
        · simp only [Config.apply, hloc, Multiset.countP_add, hq, add_zero]
          exact hI.req r k
        · simp only [Config.apply, Multiset.countP_add, hq, hl, add_zero]
          have h3 := hI.rel r k
          have h4 := he r k
          have hind : ReqP r k ((Node.rd r0, Node.sv sx, Msg.readRequest k0) :
              Node W R S × Node W R S × Msg R T V) = decide (r0 = r ∧ k0 = k) := by
            simp [ReqP]
          rw [hind] at h4
          by_cases hh : r0 = r ∧ k0 = k
          · simp only [hh, and_self, decide_true, ite_true] at h4 ⊢
            rw [← h4, Nat.mul_add] at h3; omega
          · simp only [hh, decide_false, Bool.false_eq_true, ite_false, add_zero] at h4 ⊢
            rw [← h4] at h3; omega
        · simp only [Config.apply, hloc, Multiset.countP_add, ha, add_zero]
          exact hI.ack r k
      · have hout : ∀ y ∈ outMsgs (Node.sv sx)
            (sRecv Vr (Node.sv sj) (Msg.readRelay t v r0 k0) (C.loc (Node.sv sx)).s).2,
            y.1 = Node.sv sx ∧ ∃ t' v', y.2.2 = Msg.readAck t' v' k0 := by
          intro y hy
          obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
          rw [h1] at hz
          exact ⟨rfl, sRelay_out Vr sj t v r0 k0 _ z hz⟩
        have hq : ∀ r k, (outMsgs (Node.sv sx)
            (sRecv Vr (Node.sv sj) (Msg.readRelay t v r0 k0) (C.loc (Node.sv sx)).s).2).countP
              (fun x => ReqP r k x) = 0 ∧
            (outMsgs (Node.sv sx)
            (sRecv Vr (Node.sv sj) (Msg.readRelay t v r0 k0) (C.loc (Node.sv sx)).s).2).countP
              (fun x => RelP r k x) = 0 := fun r k => by
          constructor
          · rw [countP_const _ _ false (fun y hy => by
              obtain ⟨h1, t', v', h2⟩ := hout y hy; simp [ReqP, h1])]; rfl
          · rw [countP_const _ _ false (fun y hy => by
              obtain ⟨h1, t', v', h2⟩ := hout y hy; simp [RelP, h2])]; rfl
        have he := fun r k => countP_erase_of_mem C.net _ (fun x => ReqP r k x) hmem
        have hind : ∀ r k, ReqP r k ((Node.sv sj, Node.sv sx, Msg.readRelay t v r0 k0) :
            Node W R S × Node W R S × Msg R T V) = false := fun r k => by simp [ReqP]
        refine ⟨fun r k => ?_, fun r k => ?_, fun r k => ?_⟩
        · have hne : (Node.rd r : Node W R S) ≠ Node.sv sx := by simp
          simp only [Config.apply, Multiset.countP_add, (hq r k).1, add_zero,
            Function.update_of_ne hne]
          exact hI.req r k
        · simp only [Config.apply, Multiset.countP_add, (hq r k).1, (hq r k).2, add_zero]
          have h4 := he r k
          rw [hind] at h4
          simp only [Bool.false_eq_true, ite_false, add_zero] at h4
          rw [h4]; exact hI.rel r k
        · simp only [Config.apply, Multiset.countP_add]
          have h5 := sRelay_ack Vr hfix sj t v r0 k0 (C.loc (Node.sv sx)).s r k (Node.sv sx)
          rw [← countP_outMsgs, ← h1] at h5
          have h6 := acked_update C.loc sx
            { C.loc (Node.sv sx) with
              s := (sRecv Vr (Node.sv sj) (Msg.readRelay t v r0 k0) (C.loc (Node.sv sx)).s).1 }
            (fun r k hm => by rw [h1]; exact sRelay_memb Vr sj t v r0 k0 _ r k hm) r k
          have h7 := hI.ack r k
          simp only [h1] at h5 h6 ⊢
          split_ifs at h5 h6 <;> omega
      · refine hI.quiet (fun r => by simp [Config.apply]) (fun s => ?_) _ (outMsgs_noRead h3) rfl
          (by simpa [Config.apply] using hle)
        by_cases hs : s = sx
        · subst hs; simp [Config.apply, h1, h2]
        · have hne : (Node.sv s : Node W R S) ≠ Node.sv sx := by simpa using hs
          simp [Config.apply, Function.update_of_ne hne]

lemma cinv_reach {Vr : Variant} (hfix : Vr.fixAck = true) {next : W → T → T} {v₀ : V}
    {C : Config (Node W R S) (Loc W R S T V) (Msg R T V)} {h : List (Label (Node W R S) (register V v₀))}
    (hr : (proto Vr next v₀).Reach C h) : CInv Vr C := by
  induction hr with
  | init =>
    refine ⟨fun r k => ?_, fun r k => ?_, fun r k => ?_⟩ <;> simp [Protocol.initCfg]
  | step _ hs ih => exact ih.step hfix hs

end Podc.OhRAM.Cplx

namespace Podc.OhRAM

open Cslib.SharedMemory Cslib.AsyncMP Cplx

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V]

/-- **Repaired Table 1 (read message complexity).** With line 53 nested in the `if` of line 51,
every read has at most `|S|² + 2|S|` messages, `|S|² + 3|S|` in the revised protocol. -/
theorem readMsgBound_fix (Vr : Variant) (hfix : Vr.fixAck = true) (next : W → T → T) (v₀ : V) :
    ReadMsgBound (proto (R := R) (S := S) Vr next v₀)
      (Fintype.card S ^ 2 + (if Vr.fast then 3 else 2) * Fintype.card S) := by
  intro C h hr r k
  have hI := cinv_reach hfix hr
  have h1 := countP_le_three C.sent (fun x => IsReadMsg r k x) (fun x => ReqP r k x)
    (fun x => RelP r k x) (fun x => AckP r k x) (isReadMsg_imp r k)
  have h2 := hI.req r k
  have h3 := hI.rel r k
  have h4 := hI.ack r k
  have h5 : (acked C.loc r k).card ≤ Fintype.card S := Finset.card_le_univ _
  have h2' : C.sent.countP (fun x => ReqP r k x) ≤ Fintype.card S := by
    split_ifs at h2 <;> omega
  have h6 := Nat.mul_le_mul_left (Fintype.card S + fw Vr) h2'
  unfold readMsgs
  have hm : ∀ c, (Fintype.card S + c) * Fintype.card S = Fintype.card S ^ 2 + c * Fintype.card S :=
    fun c => by rw [Nat.add_mul, pow_two]
  rw [hm] at h6
  simp only [fw] at h3 h6
  split_ifs at h3 h6 ⊢ <;> omega

/-- The repaired OhSam, OhMam (`|S|² + 2|S|`) and OhSam', OhMam' (`|S|² + 3|S|`). -/
theorem readMsgBound_fix_paper (mw fast : Bool) (next : W → T → T) (v₀ : V) :
    ReadMsgBound (proto (R := R) (S := S) ⟨mw, fast, true⟩ next v₀)
      (Fintype.card S ^ 2 + (if fast then 3 else 2) * Fintype.card S) :=
  readMsgBound_fix ⟨mw, fast, true⟩ rfl next v₀

end Podc.OhRAM
