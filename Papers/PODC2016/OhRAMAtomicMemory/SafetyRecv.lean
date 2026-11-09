import Papers.PODC2016.OhRAMAtomicMemory.SafetyInv

/-!
# The history invariant: receptions by clients

Receptions by readers (`Inv.rRecv`: a read completes in the slow path, lines 11–14, or in the
fast path of the revised protocol, lines 129–138) and by writers (`Inv.wRecv`: the end of the
discover phase of OhMam, lines 84–89, or the completion of a write, lines 27–28 / 90–91).
-/

set_option linter.unusedSectionVars false

namespace Podc.OhRAM

open Cslib.SharedMemory Cslib.AsyncMP

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V]

variable {next : W → T → T} {v₀ : V} {h : Hist W R S V v₀} {C : Cfg W R S T V}
  {Wl : List (OpId (Node W R S))} {tok : OpId (Node W R S) → T}

omit [Fintype S] [LinearOrder T] [OrderBot T] [DecidableEq V] in
lemma not_inv_ret (p : Node W R S) (v : V) :
    ∀ q o, (Label.ret p v : Label (Node W R S) (register V v₀)) ≠ .inv q o := by
  intro q o h; cases h

/-- Servers of a list of acknowledgments that agree on the tag and value. -/
lemma card_servers_const {L : List (S × T × V)} (hL : L.Nodup) {c : T × V}
    (hc : ∀ e ∈ L, e.2 = c) : (L.map Prod.fst).toFinset.card = L.length := by
  rw [List.toFinset_card_of_nodup, List.length_map]
  refine hL.map_on fun a ha b hb hab => ?_
  exact Prod.ext hab ((hc a ha).trans (hc b hb).symm)

/-- A list with at most one entry per server, viewed as a set of servers. -/
lemma Stable.of_list {C : Cfg W R S T V} {t : T} {L : List (S × T × V)}
    (hcard : maj S ≤ (L.map Prod.fst).toFinset.card)
    (htag : ∀ e ∈ L, t ≤ (C.sl e.1).tag) : Stable C t := by
  refine ⟨(L.map Prod.fst).toFinset, hcard, fun s hs => ?_⟩
  simp only [List.mem_toFinset, List.mem_map] at hs
  obtain ⟨e, he, rfl⟩ := hs
  exact htag e he

/-! ## Completion of a read -/

/-- A read of `r` completes with value `v` and tag `t`. -/
lemma Inv.rComplete (I : Inv next v₀ h C Wl tok) {r : R} (hp : (C.rl r).pending = true)
    {C' : Cfg W R S T V} (hw : ∀ w, C'.wl w = C.wl w) (hs : ∀ s, C'.sl s = C.sl s)
    (hsent : C'.sent = C.sent) (hother : ∀ r', r' ≠ r → C'.rl r' = C.rl r')
    (hpend : (C'.rl r).pending = false)
    {v : V} {t : T} (hval : ValOK h Wl tok v t)
    (hRT : ∀ a, Precedes h a (curOp h (.rd r)) → tok a ≤ t) (hst : Stable C t) :
    Inv next v₀ (h ++ [.ret (.rd r) v]) C' Wl (Function.update tok (curOp h (.rd r)) t) := by
  set h' := h ++ [(Label.ret (.rd r) v : Label (Node W R S) (register V v₀))] with hh'
  set b := curOp h (.rd r) with hb
  set tok' := Function.update tok b t with htok'
  have hcnt := I.r_cnt r
  rw [hp] at hcnt; simp only [ite_true] at hcnt
  have hbi : Invoked h b := I.r_cur_invoked hp
  have hbc : ¬ Completed h b := not_completed_curOp h _
  have hbr : opOf h b = some .read := by
    rcases I.kind hbi with ⟨w, v', h1, -⟩ | ⟨r', -, h2⟩
    · cases h1
    · exact h2
  have hops : ∀ p, opsOf h' p = opsOf h p := fun p => opsOf_append_ret h _ p v
  have hopOf : ∀ x, opOf h' x = opOf h x := fun x => opOf_append_ret h _ v x
  have hInv : ∀ x, Invoked h' x ↔ Invoked h x := by intro x; simp [Invoked, hops]
  have hcomp : ∀ x, Completed h' x ↔ Completed h x ∨ x = b := fun x => completed_append_ret x
  have hresp : ∀ x, respOf h' x = if x = b then some v else respOf h x :=
    fun x => respOf_append_ret h _ v x
  have hcur : ∀ p, p ≠ .rd r → curOp h' p = curOp h p :=
    fun p hp' => curOp_append_ret_of_ne h v (Ne.symm hp')
  have hpre : ∀ a c, Invoked h c → Precedes h' a c → Precedes h a c :=
    fun a c hc hac => hac.of_append_of_invoked hc
  have htokI : ∀ x, x ≠ b → tok' x = tok x := fun x hx => by
    rw [htok', Function.update_of_ne hx]
  have hWb : ∀ x ∈ Wl, x ≠ b := by
    rintro x hx rfl
    obtain ⟨w, h1, -⟩ := I.W_mem _ hx
    simp [hb, curOp] at h1
  have htokW : ∀ x ∈ Wl, tok' x = tok x := fun x hx => htokI x (hWb x hx)
  have htokC : ∀ x, Completed h x → tok' x = tok x := fun x hx => htokI x (by
    rintro rfl; exact hbc hx)
  have hV : ∀ v t, ValOK h Wl tok v t → ValOK h' Wl tok' v t :=
    fun v t hv => hv.mono (fun x o hx => by rw [hopOf]; exact hx) (fun _ h => h) htokW
  refine {
    wf := ?wf, sv_ops := ?sv_ops, w_ops := ?w_ops, r_ops := ?r_ops, w_cnt := ?w_cnt,
    r_cnt := ?r_cnt, w_cur_disc := ?w_cur_disc, w_cur_upd := ?w_cur_upd,
    write_resp := ?write_resp, W_nodup := I.W_nodup, W_mem := ?W_mem,
    W_complete := ?W_complete, tok_le := ?tok_le, val_s := ?val_s, val_w := ?val_w,
    val_msg := ?val_msg, read_resp := ?read_resp, prec_W := ?prec_W, prec_R := ?prec_R,
    stable := ?stable, disc_rt := ?disc_rt, read_rt := ?read_rt }
  case wf => exact I.wf.append_ret hcnt
  case sv_ops => intro s; rw [hops]; exact I.sv_ops s
  case w_ops => intro w o ho; rw [hops] at ho; exact I.w_ops w o ho
  case r_ops => intro r' o ho; rw [hops] at ho; exact I.r_ops r' o ho
  case w_cnt =>
    intro w; rw [hw, hops, respsOf_append_ret_of_ne _ _ (by simp)]; exact I.w_cnt w
  case r_cnt =>
    intro r'
    by_cases hr : r' = r
    · subst hr; rw [hpend, hops, respsOf_concat]; simp [hcnt]
    · rw [hother r' hr, hops, respsOf_append_ret_of_ne _ _ (by simp [hr])]; exact I.r_cnt r'
  case w_cur_disc =>
    intro w v' hph; rw [hw] at hph; rw [hcur _ (by simp), hopOf]; exact I.w_cur_disc w v' hph
  case w_cur_upd =>
    intro w hph; rw [hw] at hph ⊢; rw [hcur _ (by simp), hopOf]
    obtain ⟨h1, h2, h3⟩ := I.w_cur_upd w hph
    exact ⟨h1, h2, by rw [htokW _ h2]; exact h3⟩
  case write_resp =>
    intro x v' r' hx hr'
    rw [hopOf] at hx
    rw [hresp] at hr'
    split_ifs at hr' with hxb
    · subst hxb; rw [hbr] at hx; cases hx
    · exact I.write_resp x v' r' hx hr'
  case W_mem =>
    intro x hx
    obtain ⟨w, h1, h2, h3, h4⟩ := I.W_mem x hx
    refine ⟨w, h1, (hInv x).2 h2, by rw [htokW x hx]; exact h3, ?_⟩
    rw [hcur _ (by simp), hw]; exact h4
  case W_complete =>
    intro x v' hx hc
    rw [hopOf] at hx
    rcases (hcomp x).1 hc with hc | rfl
    · exact I.W_complete x v' hx hc
    · rw [hbr] at hx; cases hx
  case tok_le => intro w x hx hxw; rw [hw, htokW x hx]; exact I.tok_le w x hx hxw
  case val_s => intro s; rw [hs]; exact hV _ _ (I.val_s s)
  case val_w => intro w; rw [hw]; exact hV _ _ (I.val_w w)
  case val_msg => rw [hsent]; exact fun x hx t v h => hV _ _ (I.val_msg x hx t v h)
  case read_resp =>
    intro x r' hx hr'
    rw [hopOf] at hx
    rw [hresp] at hr'
    split_ifs at hr' with hxb
    · cases hr'; subst hxb
      rw [show tok' b = t by simp [htok']]
      exact hV _ _ hval
    · rw [htokI x hxb]; exact hV _ _ (I.read_resp x r' hx hr')
  case prec_W =>
    intro a c hac hc
    have hac' := hpre a c (I.W_mem c hc).choose_spec.2.1 hac
    rw [htokC a hac'.completed, htokW c hc]
    exact I.prec_W a c hac' hc
  case prec_R =>
    intro a c hac hc hcc
    rw [hopOf] at hc
    rcases (hcomp c).1 hcc with hcc | rfl
    · have hac' := hpre a c (I.invoked_of_completed hcc) hac
      rw [htokC a hac'.completed, htokC c hcc]
      exact I.prec_R a c hac' hc hcc
    · have hac' := hpre a _ hbi hac
      rw [htokC a hac'.completed, show tok' b = t by simp [htok']]
      exact hRT a hac'
  case stable =>
    intro a ha
    rcases (hcomp a).1 ha with ha | rfl
    · rw [htokC a ha]; exact (I.stable a ha).mono (fun s => by rw [hs])
    · rw [show tok' b = t by simp [htok']]; exact hst.mono (fun s => by rw [hs])
  case disc_rt =>
    intro w v' a hph hab
    rw [hw] at hph ⊢
    rw [hcur _ (by simp)] at hab
    have hab' := hpre a _ (I.w_cur_invoked (by rw [hph]; simp)) hab
    rw [htokC a hab'.completed]
    obtain ⟨Q, hQ, hQt, hQm⟩ := I.disc_rt w v' a hph hab'
    exact ⟨Q, hQ, fun s hs' => by rw [hs]; exact hQt s hs',
      fun s hs' t v'' hm => hQm s hs' t v'' (by rw [hsent] at hm; exact hm)⟩
  case read_rt =>
    intro r' a hp' hab
    by_cases hr : r' = r
    · subst hr; rw [hpend] at hp'; cases hp'
    · rw [hother r' hr] at hp' ⊢
      rw [hcur _ (by simp [hr])] at hab
      have hab' := hpre a _ (I.r_cur_invoked hp') hab
      rw [htokC a hab'.completed]
      obtain ⟨Q, hQ, hQt, hii, hiii, hiv⟩ := I.read_rt r' a hp' hab'
      exact ⟨Q, hQ, fun s hs' => by rw [hs]; exact hQt s hs',
        fun s hs' d t v hm => hii s hs' d t v (by rw [hsent] at hm; exact hm),
        fun sx => by rw [hs]; exact hiii sx,
        fun sx t v hm => hiv sx t v (by rw [hsent] at hm; exact hm)⟩

/-- **Receptions by readers.** Lemmas 2–4, 7, 9, 10 (slow path: the minimum tag of a majority
of `readAck`s is at least the tag of every preceding operation) and Lemmas 14, 15, 18, 19 (fast
path: a majority of relays with the same tag meets the quorum of every preceding operation). -/
lemma Inv.rRecv {Vr : Variant} (hlt : ∀ w t, t < next w t)
    (hinj : ∀ w w' t t', next w t = next w' t' → w = w') (I : Inv next v₀ h C Wl tok)
    (IC : CInv Vr C) {r : R} {s : S} {m : Msg R T V} (hx : (Node.sv s, Node.rd r, m) ∈ C.net) :
    ∃ tok', Inv next v₀ (h ++ ((rWait Vr v₀ (rRecord Vr s m (C.rl r))).2.map
      (Label.ret (.rd r))).toList)
      (C.setR r (rWait Vr v₀ (rRecord Vr s m (C.rl r))).1 0 (C.net.erase (Node.sv s, Node.rd r, m)))
      Wl tok' := by
  have IC' := IC.rRecv (v₀ := v₀) hx
  set l1 := rRecord Vr s m (C.rl r) with hl1
  set C' := C.setR r (rWait Vr v₀ l1).1 0 (C.net.erase (Node.sv s, Node.rd r, m)) with hC'
  have hw : ∀ w, C'.wl w = C.wl w := by simp [hC']
  have hs : ∀ s, C'.sl s = C.sl s := by simp [hC']
  have hsent : C'.sent = C.sent := by simp [hC']
  have hother : ∀ r', r' ≠ r → C'.rl r' = C.rl r' := by intro r' h; simp [hC', h]
  have hself : C'.rl r = (rWait Vr v₀ l1).1 := by simp [hC']
  have hop : (C'.rl r).op = (C.rl r).op := by rw [hself]; simp [hl1]
  have hack : (C'.rl r).ack = l1.ack := by rw [hself]; simp
  have hrel : (C'.rl r).relay = l1.relay := by rw [hself]; simp
  have hmsg : ∀ e ∈ l1.ack, (Node.sv e.1, Node.rd r, Msg.readAck e.2.1 e.2.2 (C.rl r).op) ∈ C.sent := by
    intro e he
    have := IC'.rack_sent r e (by rw [hack]; exact he)
    rwa [hop, hsent] at this
  have hrmsg : ∀ e ∈ l1.relay,
      (Node.sv e.1, Node.rd r, Msg.readRelay e.2.1 e.2.2 r (C.rl r).op) ∈ C.sent := by
    intro e he
    obtain ⟨r', h1⟩ := IC'.rrel_sent r e (by rw [hrel]; exact he)
    rw [hop, hsent] at h1
    have := IC.rel_dst _ _ _ _ _ _ h1
    subst this; exact h1
  rcases rWait_cases (Vr := Vr) (v₀ := v₀) l1 with h1 | ⟨hp, hlen, h1⟩ | ⟨v, hp, -, hfv, h1⟩
  · refine ⟨tok, ?_⟩
    rw [h1]
    simp only [Option.map_none, Option.toList_none, List.append_nil]
    refine I.congr (by simp [hw]) (by simp [hw]) (by simp [hw]) (by simp [hw]) (fun r' => ?_)
      (fun r' => ?_) hs hsent
    · by_cases hr : r' = r
      · subst hr; rw [hself, h1, hl1, rRecord_pending]
      · rw [hother r' hr]
    · by_cases hr : r' = r
      · subst hr; exact hop
      · rw [hother r' hr]
  · -- slow path: the minimum tag of `rAck`
    rw [hl1, rRecord_pending] at hp
    have hne : l1.ack ≠ [] := by
      intro h0; rw [h0] at hlen; have := maj_pos (S := S); simp at hlen; omega
    obtain ⟨e, he, hv, hmin⟩ := minVal_spec v₀ hne
    have hpend : (C'.rl r).pending = false := by rw [hself, h1]
    have hcnt : ∀ s', l1.ack.countP (fun e => decide (e.1 = s')) ≤ 1 := by
      intro s'
      have := IC'.rack_tok s' r
      rw [hack] at this
      split_ifs at this <;> omega
    refine ⟨Function.update tok (curOp h (.rd r)) e.2.1, ?_⟩
    rw [h1, hv]
    refine I.rComplete hp hw hs hsent hother hpend (I.val_msg _ (hmsg e he) _ _ rfl)
      (fun a hab => ?_) ?_
    · obtain ⟨Q, -, -, -, -, hiv⟩ := I.read_rt r a hp hab
      exact hiv _ _ _ (hmsg e he)
    · refine Stable.of_list (L := l1.ack) (by rw [card_servers hcnt, hlen]) fun e' he' => ?_
      exact (hmin e' he').trans (IC.tag_le _ _ _ _ _ (hmsg e' he') rfl)
  · -- fast path: a majority of relays with the same tag
    rw [hl1, rRecord_pending] at hp
    obtain ⟨p, hp', rfl, hZ⟩ := fastVal_spec hfv
    have hpend : (C'.rl r).pending = false := by rw [hself, h1]
    set Z := l1.relay.filter (fun q => decide (q.2.1 = p.2.1)) with hZdef
    have hZmem : ∀ e ∈ Z, e ∈ l1.relay ∧ e.2.1 = p.2.1 := by
      intro e he; simpa [hZdef] using he
    have hvp := I.val_msg _ (hrmsg p hp') _ _ rfl
    have hZc : ∀ e ∈ Z, e.2 = (p.2.1, p.2.2) := by
      intro e he
      obtain ⟨he1, he2⟩ := hZmem e he
      have hve := I.val_msg _ (hrmsg e he1) _ _ rfl
      rw [he2] at hve
      exact Prod.ext he2 (I.val_unique hlt hinj hve hvp)
    have hZnd : Z.Nodup := by
      have := IC'.rrel_nodup r; rw [hrel] at this; exact this.filter _
    have hZcard : maj S ≤ (Z.map Prod.fst).toFinset.card := by
      rw [card_servers_const hZnd hZc]; exact hZ
    refine ⟨Function.update tok (curOp h (.rd r)) p.2.1, ?_⟩
    rw [h1]
    refine I.rComplete hp hw hs hsent hother hpend hvp (fun a hab => ?_) ?_
    · obtain ⟨Q, hQ, -, hii, -, -⟩ := I.read_rt r a hp hab
      obtain ⟨s', hs'⟩ := maj_inter hQ hZcard
      rw [Finset.mem_inter, List.mem_toFinset, List.mem_map] at hs'
      obtain ⟨hsQ, e, he, rfl⟩ := hs'
      obtain ⟨he1, he2⟩ := hZmem e he
      rw [← he2]
      exact hii e.1 hsQ _ _ _ (hrmsg e he1)
    · refine Stable.of_list hZcard fun e he => ?_
      obtain ⟨he1, he2⟩ := hZmem e he
      rw [← he2]
      exact IC.tag_le _ _ _ _ _ (hrmsg e he1) rfl

/-! ## Receptions by writers -/

/-- **End of the discover phase of OhMam** (lines 84–89). Lemmas 8, 11, 20, 21: the new tag
`⟨maxTS + 1, w⟩` is larger than the tag of every preceding operation, since the `discoverAck`s
of a majority meet the quorum of every preceding operation. -/
lemma Inv.wDisc {Vr : Variant} (hlt : ∀ w t, t < next w t) (I : Inv next v₀ h C Wl tok)
    (IC : CInv Vr C) {w : W} {s : S} {m : Msg R T V} (hx : (Node.sv s, Node.wr w, m) ∈ C.net)
    {val : V} (hph : (wRecord Vr s m (C.wl w)).phase = .disc val)
    (hlen : (wRecord Vr s m (C.wl w)).ack.length = maj S) :
    Inv next v₀ h
      (C.setW w { wRecord Vr s m (C.wl w) with
          tag := next w (maxTag (wRecord Vr s m (C.wl w)).ack), val := val,
          op := (wRecord Vr s m (C.wl w)).op + 1, ack := [], phase := .upd }
        (bcast (.writeRequest (next w (maxTag (wRecord Vr s m (C.wl w)).ack)) val
          ((wRecord Vr s m (C.wl w)).op + 1)))
        (C.net.erase (Node.sv s, Node.wr w, m)))
      (Wl ++ [curOp h (.wr w)])
      (Function.update tok (curOp h (.wr w)) (next w (maxTag (wRecord Vr s m (C.wl w)).ack))) := by
  obtain ⟨hA, -, hT⟩ := IC.wRecord_ack hx
  set l1 := wRecord Vr s m (C.wl w) with hl1
  have hph0 : (C.wl w).phase = .disc val := by rw [← hph, hl1, wRecord_phase]
  have hmw : Vr.mw = true := IC.disc_mw w val hph0
  set nt := next w (maxTag l1.ack) with hnt
  set b := curOp h (.wr w) with hb
  set tok' := Function.update tok b nt with htok'
  set C' := C.setW w { l1 with tag := nt, val := val, op := l1.op + 1, ack := [], phase := .upd }
    (bcast (.writeRequest nt val (l1.op + 1))) (C.net.erase (Node.sv s, Node.wr w, m)) with hC'
  have hsent : C'.sent = C.sent + outMsgs (.wr w) (bcast (.writeRequest nt val (l1.op + 1))) := rfl
  have hr : ∀ r, C'.rl r = C.rl r := by simp [hC']
  have hs : ∀ s, C'.sl s = C.sl s := by simp [hC']
  have hother : ∀ w', w' ≠ w → C'.wl w' = C.wl w' := by intro w' h; simp [hC', h]
  have hself : C'.wl w =
      { l1 with tag := nt, val := val, op := l1.op + 1, ack := [], phase := .upd } := by
    simp [hC']
  have hsv : ∀ s d m, (Node.sv s, d, m) ∈ C'.sent → (Node.sv s, d, m) ∈ C.sent := by
    intro s d m hm; simpa [hC'] using hm
  have hbi : Invoked h b := I.w_cur_invoked (by rw [hph0]; simp)
  have hbc : ¬ Completed h b := not_completed_curOp h _
  have hbo : opOf h b = some (.write val) := I.w_cur_disc w val hph0
  have hbW : b ∉ Wl := by
    intro hbW
    obtain ⟨w', h1, -, -, h4⟩ := I.W_mem b hbW
    simp only [hb, curOp, Node.wr.injEq] at h1; subst h1
    have := h4 rfl; rw [hph0] at this; cases this
  have htokI : ∀ x, x ≠ b → tok' x = tok x := fun x hx => by
    rw [htok', Function.update_of_ne hx]
  have htokW : ∀ x ∈ Wl, tok' x = tok x := fun x hx => htokI x (by rintro rfl; exact hbW hx)
  have htokC : ∀ x, Completed h x → tok' x = tok x :=
    fun x hx => htokI x (by rintro rfl; exact hbc hx)
  have htb : tok' b = nt := by simp [htok']
  -- the key step: the discovered maximum is at least the tag of every preceding operation
  have hcnt : ∀ s', l1.ack.countP (fun e => decide (e.1 = s')) ≤ 1 := by
    intro s'; have := hT hmw s'; omega
  have hRT : ∀ a, Precedes h a b → tok a < nt := by
    intro a hab
    obtain ⟨Q, hQ, -, hQm⟩ := I.disc_rt w val a hph0 hab
    obtain ⟨s', hs'⟩ := maj_inter hQ (show maj S ≤ (l1.ack.map Prod.fst).toFinset.card by
      rw [card_servers hcnt, hlen])
    rw [Finset.mem_inter, List.mem_toFinset, List.mem_map] at hs'
    obtain ⟨hsQ, e, he, rfl⟩ := hs'
    have hsent_e := hA e he
    unfold WAckSent at hsent_e
    rw [ite_eq_left hmw] at hsent_e
    rcases hsent_e with hm | hm
    · have := (IC.wack_le hmw _ _ _ _ _ hm).2 rfl
      rw [hph0] at this; cases this.1
    · exact (hQm e.1 hsQ _ _ hm).trans_lt ((le_maxTag he).trans_lt (hlt w _))
  have hV : ∀ v t, ValOK h Wl tok v t → ValOK h (Wl ++ [b]) tok' v t :=
    fun v t hv => hv.mono (fun _ _ h => h) (fun x h => List.mem_append_left _ h) htokW
  have hVb : ValOK h (Wl ++ [b]) tok' val nt := Or.inr ⟨b, by simp, htb, hbo⟩
  refine {
    wf := I.wf, sv_ops := I.sv_ops, w_ops := I.w_ops, r_ops := I.r_ops, w_cnt := ?w_cnt,
    r_cnt := ?r_cnt, w_cur_disc := ?w_cur_disc, w_cur_upd := ?w_cur_upd,
    write_resp := I.write_resp, W_nodup := ?W_nodup, W_mem := ?W_mem,
    W_complete := fun x v hx hc => List.mem_append_left _ (I.W_complete x v hx hc),
    tok_le := ?tok_le, val_s := ?val_s, val_w := ?val_w,
    val_msg := ?val_msg, read_resp := ?read_resp, prec_W := ?prec_W, prec_R := ?prec_R,
    stable := ?stable, disc_rt := ?disc_rt, read_rt := ?read_rt }
  case w_cnt =>
    intro w'
    by_cases hw : w' = w
    · subst hw; rw [hself]; have := I.w_cnt w'; rw [hph0] at this; simpa using this
    · rw [hother w' hw]; exact I.w_cnt w'
  case r_cnt => intro r; rw [hr]; exact I.r_cnt r
  case w_cur_disc =>
    intro w' v hph'
    by_cases hw : w' = w
    · subst hw; rw [hself] at hph'; cases hph'
    · rw [hother w' hw] at hph'; exact I.w_cur_disc w' v hph'
  case w_cur_upd =>
    intro w' hph'
    by_cases hw : w' = w
    · subst hw; rw [hself]
      exact ⟨hbo, List.mem_append_right _ (List.mem_singleton.2 rfl), htb⟩
    · rw [hother w' hw] at hph' ⊢
      obtain ⟨h1, h2, h3⟩ := I.w_cur_upd w' hph'
      exact ⟨h1, List.mem_append_left _ h2, by rw [htokW _ h2]; exact h3⟩
  case W_nodup => rw [← List.concat_eq_append]; exact I.W_nodup.concat hbW
  case W_mem =>
    intro x hx
    rcases List.mem_append.1 hx with hx1 | hx1
    · obtain ⟨w', h1, h2, h3, h4⟩ := I.W_mem x hx1
      refine ⟨w', h1, h2, by rw [htokW x hx1]; exact h3, fun hxc => ?_⟩
      by_cases hw : w' = w
      · subst hw; rw [hself]; rfl
      · rw [hother w' hw]; exact h4 hxc
    · rw [List.mem_singleton] at hx1; rw [hx1]
      exact ⟨w, rfl, hbi, ⟨maxTag l1.ack, htb⟩, fun _ => by rw [hself]; rfl⟩
  case tok_le =>
    intro w' x hx hxw
    rcases List.mem_append.1 hx with hx1 | hx1
    · rw [htokW x hx1]
      by_cases hw : w' = w
      · subst hw; rw [hself]
        have hxb : x ≠ b := by rintro rfl; exact hbW hx1
        obtain ⟨p, i⟩ := x
        simp only at hxw; subst hxw
        have hxi := (I.W_mem _ hx1).choose_spec.2.1
        have hcnt' := I.w_cnt w'
        rw [hph0] at hcnt'
        simp only [Invoked] at hxi
        have hi : i < (respsOf h (.wr w')).length := by
          have : i ≠ (respsOf h (.wr w')).length := fun h' => hxb (by rw [hb, curOp, h'])
          simp at hcnt'; omega
        exact (hRT _ (I.wf.precedes_of_lt hi hbi)).le
      · rw [hother w' hw]; exact I.tok_le w' x hx1 hxw
    · rw [List.mem_singleton] at hx1; rw [hx1] at hxw ⊢
      simp only [hb, curOp, Node.wr.injEq] at hxw; subst hxw
      rw [hself, htb]
  case val_s => intro s; rw [hs]; exact hV _ _ (I.val_s s)
  case val_w =>
    intro w'
    by_cases hw : w' = w
    · subst hw; rw [hself]; exact hVb
    · rw [hother w' hw]; exact hV _ _ (I.val_w w')
  case val_msg =>
    rintro ⟨a, b', c⟩ hm t v htv
    rw [hsent, Multiset.mem_add, mem_outMsgs_iff, mem_bcast_iff] at hm
    rcases hm with hm | ⟨-, -, rfl⟩
    · exact hV _ _ (I.val_msg _ hm t v htv)
    · simp only [Msg.tv_writeRequest, Option.some.injEq, Prod.mk.injEq] at htv
      obtain ⟨rfl, rfl⟩ := htv; exact hVb
  case read_resp =>
    intro x r' hx hr'
    rw [htokC x (Completed.of_respOf_eq_some hr')]
    exact hV _ _ (I.read_resp x r' hx hr')
  case prec_W =>
    intro a c hac hc
    rw [htokC a hac.completed]
    rcases List.mem_append.1 hc with hc1 | hc1
    · rw [htokW c hc1]; exact I.prec_W a c hac hc1
    · rw [List.mem_singleton] at hc1; subst hc1; rw [htb]; exact hRT a hac
  case prec_R =>
    intro a c hac hc hcc
    rw [htokC a hac.completed, htokC c hcc]; exact I.prec_R a c hac hc hcc
  case stable =>
    intro a ha; rw [htokC a ha]; exact (I.stable a ha).mono (fun s => by rw [hs])
  case disc_rt =>
    intro w' v a hph' hab
    by_cases hw : w' = w
    · subst hw; rw [hself] at hph'; cases hph'
    · rw [hother w' hw] at hph' ⊢
      rw [htokC a hab.completed]
      obtain ⟨Q, hQ, hQt, hQm⟩ := I.disc_rt w' v a hph' hab
      exact ⟨Q, hQ, fun s hs' => by rw [hs]; exact hQt s hs',
        fun s hs' t v' hm => hQm s hs' t v' (hsv _ _ _ hm)⟩
  case read_rt =>
    intro r a hp hab
    rw [hr] at hp ⊢
    rw [htokC a hab.completed]
    obtain ⟨Q, hQ, hQt, hii, hiii, hiv⟩ := I.read_rt r a hp hab
    exact ⟨Q, hQ, fun s hs' => by rw [hs]; exact hQt s hs',
      fun s hs' d t v hm => hii s hs' d t v (hsv _ _ _ hm), fun sx => by rw [hs]; exact hiii sx,
      fun sx t v hm => hiv sx t v (hsv _ _ _ hm)⟩

/-- **Completion of a write** (lines 27–28 / 90–91): a majority of servers has a tag at least the
tag of the write (Lemmas 3, 9 and their analogues: the senders of the `writeAck`s). -/
lemma Inv.wComplete {Vr : Variant} (hlt : ∀ w t, t < next w t)
    (hinj : ∀ w w' t t', next w t = next w' t' → w = w') (I : Inv next v₀ h C Wl tok)
    (IC : CInv Vr C) {w : W} {s : S} {m : Msg R T V} (hx : (Node.sv s, Node.wr w, m) ∈ C.net)
    (hph : (wRecord Vr s m (C.wl w)).phase = .upd)
    (hlen : (wRecord Vr s m (C.wl w)).ack.length = maj S) :
    Inv next v₀ (h ++ [.ret (.wr w) (wRecord Vr s m (C.wl w)).val])
      (C.setW w { wRecord Vr s m (C.wl w) with phase := .idle } 0
        (C.net.erase (Node.sv s, Node.wr w, m))) Wl tok := by
  obtain ⟨hA, hN, hT⟩ := IC.wRecord_ack hx
  set l1 := wRecord Vr s m (C.wl w) with hl1
  have hph0 : (C.wl w).phase = .upd := by rw [← hph, hl1, wRecord_phase]
  have hval1 : l1.val = (C.wl w).val := by rw [hl1, wRecord_val]
  rw [hval1]
  set h' := h ++ [(Label.ret (.wr w) (C.wl w).val : Label (Node W R S) (register V v₀))] with hh'
  set b := curOp h (.wr w) with hb
  set C' := C.setW w { l1 with phase := .idle } 0 (C.net.erase (Node.sv s, Node.wr w, m)) with hC'
  have hsent : C'.sent = C.sent := by simp [hC']
  have hr : ∀ r, C'.rl r = C.rl r := by simp [hC']
  have hs : ∀ s, C'.sl s = C.sl s := by simp [hC']
  have hother : ∀ w', w' ≠ w → C'.wl w' = C.wl w' := by intro w' h; simp [hC', h]
  have hself : C'.wl w = { l1 with phase := .idle } := by simp [hC']
  have htag : (C'.wl w).tag = (C.wl w).tag := by rw [hself, hl1, wRecord_tag]
  have hval' : (C'.wl w).val = (C.wl w).val := by rw [hself, hl1, wRecord_val]
  obtain ⟨hbo, hbW, htb⟩ := I.w_cur_upd w hph0
  have hcnt := I.w_cnt w
  rw [hph0] at hcnt; simp only [reduceCtorEq, ite_false] at hcnt
  have hbi : Invoked h b := I.w_cur_invoked (by rw [hph0]; simp)
  -- the senders of the acknowledgments: a majority with tags `≥ tok b`
  have hst : Stable C (tok b) := by
    rw [htb]
    by_cases hmw : Vr.mw = true
    · have hc : ∀ s', l1.ack.countP (fun e => decide (e.1 = s')) ≤ 1 := by
        intro s'; have := hT hmw s'; omega
      refine Stable.of_list (L := l1.ack) (by rw [card_servers hc, hlen]) fun e he => ?_
      have hse := hA e he
      unfold WAckSent at hse
      rw [ite_eq_left hmw] at hse
      rcases hse with hm | hm
      · exact ((IC.wack_le hmw _ _ _ _ _ hm).2 rfl).2.trans (IC.tag_le _ _ _ _ _ hm rfl)
      · have := (IC.dack_le hmw _ _ _ _ _ hm).2 rfl
        rw [hph0] at this; cases this
    · have hc : ∀ e ∈ l1.ack, e.2 = ((C.wl w).tag, (C.wl w).val) := by
        intro e he
        have hse := hA e he
        unfold WAckSent at hse
        rw [ite_eq_right hmw] at hse
        obtain ⟨⟨k, hm⟩, he2⟩ := hse
        have hv := I.val_msg _ hm _ _ rfl
        rw [he2] at hv
        exact Prod.ext he2 (I.val_unique hlt hinj hv (I.val_w w))
      refine Stable.of_list (L := l1.ack) (by rw [card_servers_const hN hc, hlen])
        fun e he => ?_
      have hse := hA e he
      unfold WAckSent at hse
      rw [ite_eq_right hmw] at hse
      obtain ⟨⟨k, hm⟩, he2⟩ := hse
      rw [← he2]
      exact IC.tag_le _ _ _ _ _ hm rfl
  have hops : ∀ p, opsOf h' p = opsOf h p := fun p => opsOf_append_ret h _ p _
  have hopOf : ∀ x, opOf h' x = opOf h x := fun x => opOf_append_ret h _ _ x
  have hInv : ∀ x, Invoked h' x ↔ Invoked h x := by intro x; simp [Invoked, hops]
  have hcomp : ∀ x, Completed h' x ↔ Completed h x ∨ x = b := fun x => completed_append_ret x
  have hresp : ∀ x, respOf h' x = if x = b then some (C.wl w).val else respOf h x :=
    fun x => respOf_append_ret h _ _ x
  have hcur : ∀ p, p ≠ .wr w → curOp h' p = curOp h p :=
    fun p hp' => curOp_append_ret_of_ne h _ (Ne.symm hp')
  have hpre : ∀ a c, Invoked h c → Precedes h' a c → Precedes h a c :=
    fun a c hc hac => hac.of_append_of_invoked hc
  have hV : ∀ v t, ValOK h Wl tok v t → ValOK h' Wl tok v t :=
    fun v t hv => hv.mono (fun x o hx => by rw [hopOf]; exact hx) (fun _ h => h) (fun _ _ => rfl)
  refine {
    wf := I.wf.append_ret hcnt, sv_ops := ?sv_ops, w_ops := ?w_ops, r_ops := ?r_ops,
    w_cnt := ?w_cnt, r_cnt := ?r_cnt, w_cur_disc := ?w_cur_disc, w_cur_upd := ?w_cur_upd,
    write_resp := ?write_resp, W_nodup := I.W_nodup, W_mem := ?W_mem,
    W_complete := ?W_complete, tok_le := ?tok_le, val_s := ?val_s, val_w := ?val_w,
    val_msg := ?val_msg, read_resp := ?read_resp, prec_W := ?prec_W, prec_R := ?prec_R,
    stable := ?stable, disc_rt := ?disc_rt, read_rt := ?read_rt }
  case sv_ops => intro s; rw [hops]; exact I.sv_ops s
  case w_ops => intro w o ho; rw [hops] at ho; exact I.w_ops w o ho
  case r_ops => intro r' o ho; rw [hops] at ho; exact I.r_ops r' o ho
  case w_cnt =>
    intro w'
    by_cases hw : w' = w
    · subst hw; rw [hself, hops, respsOf_concat]; simp [hcnt]
    · rw [hother w' hw, hops, respsOf_append_ret_of_ne _ _ (by simp [hw])]; exact I.w_cnt w'
  case r_cnt =>
    intro r; rw [hr, hops, respsOf_append_ret_of_ne _ _ (by simp)]; exact I.r_cnt r
  case w_cur_disc =>
    intro w' v hph'
    by_cases hw : w' = w
    · subst hw; rw [hself] at hph'; cases hph'
    · rw [hother w' hw] at hph'; rw [hcur _ (by simp [hw]), hopOf]; exact I.w_cur_disc w' v hph'
  case w_cur_upd =>
    intro w' hph'
    by_cases hw : w' = w
    · subst hw; rw [hself] at hph'; cases hph'
    · rw [hother w' hw] at hph' ⊢; rw [hcur _ (by simp [hw]), hopOf]; exact I.w_cur_upd w' hph'
  case write_resp =>
    intro x v r' hx hr'
    rw [hopOf] at hx
    rw [hresp] at hr'
    split_ifs at hr' with hxb
    · cases hr'; subst hxb; rw [hbo] at hx; cases hx; rfl
    · exact I.write_resp x v r' hx hr'
  case W_mem =>
    intro x hx
    obtain ⟨w', h1, h2, h3, h4⟩ := I.W_mem x hx
    refine ⟨w', h1, (hInv x).2 h2, h3, fun hxc => ?_⟩
    by_cases hw : w' = w
    · subst hw; rw [hself]; rfl
    · rw [hother w' hw]; rw [hcur _ (by simp [hw])] at hxc; exact h4 hxc
  case W_complete =>
    intro x v hx hc
    rw [hopOf] at hx
    rcases (hcomp x).1 hc with hc | rfl
    · exact I.W_complete x v hx hc
    · exact hbW
  case tok_le =>
    intro w' x hxW hxw
    by_cases hw : w' = w
    · subst hw; rw [htag]; exact I.tok_le w' x hxW hxw
    · rw [hother w' hw]; exact I.tok_le w' x hxW hxw
  case val_s => intro s; rw [hs]; exact hV _ _ (I.val_s s)
  case val_w =>
    intro w'
    by_cases hw : w' = w
    · subst hw; rw [htag, hval']; exact hV _ _ (I.val_w w')
    · rw [hother w' hw]; exact hV _ _ (I.val_w w')
  case val_msg => rw [hsent]; exact fun x hx t v h => hV _ _ (I.val_msg x hx t v h)
  case read_resp =>
    intro x r' hx hr'
    rw [hopOf] at hx
    rw [hresp] at hr'
    split_ifs at hr' with hxb
    · subst hxb; rw [hbo] at hx; cases hx
    · exact hV _ _ (I.read_resp x r' hx hr')
  case prec_W =>
    intro a c hac hc
    exact I.prec_W a c (hpre a c (I.W_mem c hc).choose_spec.2.1 hac) hc
  case prec_R =>
    intro a c hac hc hcc
    rw [hopOf] at hc
    rcases (hcomp c).1 hcc with hcc | rfl
    · exact I.prec_R a c (hpre a c (I.invoked_of_completed hcc) hac) hc hcc
    · rw [hbo] at hc; cases hc
  case stable =>
    intro a ha
    rcases (hcomp a).1 ha with ha | rfl
    · exact (I.stable a ha).mono (fun s => by rw [hs])
    · exact hst.mono (fun s => by rw [hs])
  case disc_rt =>
    intro w' v a hph' hab
    by_cases hw : w' = w
    · subst hw; rw [hself] at hph'; cases hph'
    · rw [hother w' hw] at hph' ⊢
      rw [hcur _ (by simp [hw])] at hab
      have hab' := hpre a _ (I.w_cur_invoked (by rw [hph']; simp)) hab
      obtain ⟨Q, hQ, hQt, hQm⟩ := I.disc_rt w' v a hph' hab'
      exact ⟨Q, hQ, fun s hs' => by rw [hs]; exact hQt s hs',
        fun s hs' t v' hm => hQm s hs' t v' (by rw [hsent] at hm; exact hm)⟩
  case read_rt =>
    intro r a hp hab
    rw [hr] at hp ⊢
    rw [hcur _ (by simp)] at hab
    have hab' := hpre a _ (I.r_cur_invoked hp) hab
    obtain ⟨Q, hQ, hQt, hii, hiii, hiv⟩ := I.read_rt r a hp hab'
    exact ⟨Q, hQ, fun s hs' => by rw [hs]; exact hQt s hs',
      fun s hs' d t v hm => hii s hs' d t v (by rw [hsent] at hm; exact hm),
      fun sx => by rw [hs]; exact hiii sx,
      fun sx t v hm => hiv sx t v (by rw [hsent] at hm; exact hm)⟩

/-- **Receptions by writers.** -/
lemma Inv.wRecv {Vr : Variant} (hlt : ∀ w t, t < next w t)
    (hinj : ∀ w w' t t', next w t = next w' t' → w = w') (I : Inv next v₀ h C Wl tok)
    (IC : CInv Vr C) {w : W} {s : S} {m : Msg R T V} (hx : (Node.sv s, Node.wr w, m) ∈ C.net) :
    ∃ Wl' tok', Inv next v₀ (h ++ ((wWait (R := R) next w (wRecord Vr s m (C.wl w))).2.2.map
      (Label.ret (.wr w))).toList)
      (C.setW w (wWait (R := R) next w (wRecord Vr s m (C.wl w))).1
        (wWait (R := R) next w (wRecord Vr s m (C.wl w))).2.1
        (C.net.erase (Node.sv s, Node.wr w, m))) Wl' tok' := by
  rcases wWait_cases (R := R) (next := next) w (wRecord Vr s m (C.wl w)) with h1 |
    ⟨val, hlen, hph, h1⟩ | ⟨hlen, hph, h1⟩ <;> rw [h1]
  · refine ⟨Wl, tok, ?_⟩
    simp only [Option.map_none, Option.toList_none, List.append_nil]
    refine I.congr (fun w' => ?_) (fun w' => ?_) (fun w' => ?_) (fun w' => ?_) (by simp)
      (by simp) (by simp) (by simp)
    all_goals
      by_cases hw : w' = w
      · subst hw; simp
      · simp [hw]
  · exact ⟨_, _, by simpa using I.wDisc hlt IC hx hph hlen⟩
  · exact ⟨Wl, tok, by simpa using I.wComplete hlt hinj IC hx hph hlen⟩

end Podc.OhRAM
