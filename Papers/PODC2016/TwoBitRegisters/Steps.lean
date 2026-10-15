import Papers.PODC2016.TwoBitRegisters.Algorithm

/-!
# Step lemmas for the algorithm of Figure 1

Characterizations of the individual transitions of `alg w t v₀`, and basic facts on the messages
sent (`sendTo`, `outMsgs`).
-/

set_option linter.unusedSectionVars false

namespace Podc.TwoBit

open Cslib.SharedMemory Cslib.AsyncMP

variable {P V : Type} [Fintype P] [DecidableEq P] [DecidableEq V]

/-! ## Sent messages -/

lemma mem_outMsgs_sendTo {c : P → Prop} [DecidablePred c] {m : Msg V} {p : P}
    {x : P × P × Msg V} : x ∈ outMsgs p (sendTo c m) ↔ x.1 = p ∧ c x.2.1 ∧ x.2.2 = m := by
  obtain ⟨a, b, d⟩ := x
  simp only [outMsgs, sendTo, Multiset.map_map, Function.comp_def, Multiset.mem_map,
    Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨ℓ, hℓ, rfl, rfl, rfl⟩; exact ⟨rfl, hℓ, rfl⟩
  · rintro ⟨rfl, hb, rfl⟩; exact ⟨b, hb, rfl, rfl, rfl⟩

lemma count_outMsgs_sendTo {c : P → Prop} [DecidablePred c] {m : Msg V} {p : P}
    (x : P × P × Msg V) :
    (outMsgs p (sendTo c m)).count x = if x.1 = p ∧ c x.2.1 ∧ x.2.2 = m then 1 else 0 := by
  rw [Multiset.count_eq_of_nodup]
  · simp only [mem_outMsgs_sendTo]
  · simp only [outMsgs, sendTo, Multiset.map_map, Function.comp_def]
    refine Multiset.Nodup.map ?_ (Finset.nodup _)
    intro a b h; simpa using h

lemma mem_outMsgs_single {p q : P} {m : Msg V} {x : P × P × Msg V} :
    x ∈ outMsgs p ({(q, m)} : Multiset (P × Msg V)) ↔ x = (p, q, m) := by
  simp [outMsgs]

lemma count_outMsgs_single {p q : P} {m : Msg V} (x : P × P × Msg V) :
    (outMsgs p ({(q, m)} : Multiset (P × Msg V))).count x = if x = (p, q, m) then 1 else 0 := by
  simp [outMsgs, Multiset.count_singleton]

@[simp] lemma outMsgs_zero {p : P} : outMsgs p (0 : Multiset (P × Msg V)) = 0 := rfl

/-! ## Transitions -/

variable {w : P} {t : ℕ} {v₀ : V}
variable {C C' : Config P (Loc P V) (Msg V)} {ℓ : Option (Label P (register V v₀))}

lemma step_inv {p : P} {o : RWOp V}
    (h : (alg w t v₀).step C (.inv p o) = some (C', ℓ)) :
    p ∉ C.crashed ∧ ℓ = some (.inv p o) ∧
      ∃ l out, invoke w p o (C.loc p) = some (l, out) ∧ C' = C.apply p l out C.net := by
  simp only [Protocol.step] at h
  split_ifs at h with hp
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨l, out⟩, h1, rfl, rfl⟩ := h
  exact ⟨hp, rfl, l, out, h1, rfl⟩

lemma step_internal {p : P} {a : Act P}
    (h : (alg w t v₀).step C (.internal p a) = some (C', ℓ)) :
    p ∉ C.crashed ∧ ∃ l out r, internal (Fintype.card P - t) p a (C.loc p) = some (l, out, r) ∧
      C' = C.apply p l out C.net ∧ ℓ = r.map (Label.ret p) := by
  simp only [Protocol.step] at h
  split_ifs at h with hp
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨l, out, r⟩, h1, rfl, rfl⟩ := h
  exact ⟨hp, l, out, r, h1, rfl, rfl⟩

lemma step_recv {src dst : P} {m : Msg V}
    (h : (alg w t v₀).step C (.recv src dst m) = some (C', ℓ)) :
    dst ∉ C.crashed ∧ (src, dst, m) ∈ C.net ∧ ∃ l out r, receive dst src m (C.loc dst) = some (l, out, r) ∧
      C' = C.apply dst l out (C.net.erase (src, dst, m)) ∧ ℓ = r.map (Label.ret dst) := by
  simp only [Protocol.step] at h
  split_ifs at h with hp
  push Not at hp
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨⟨l, out, r⟩, h1, rfl, rfl⟩ := h
  exact ⟨hp.1, hp.2, l, out, r, h1, rfl, rfl⟩

lemma step_drop {src dst : P} {m : Msg V}
    (h : (alg w t v₀).step C (.drop src dst m) = some (C', ℓ)) :
    src ∈ C.crashed ∧ (src, dst, m) ∈ C.net ∧ ℓ = none ∧
      C' = ⟨C.loc, C.net.erase (src, dst, m), C.sent, C.crashed⟩ := by
  simp only [Protocol.step] at h
  split_ifs at h with hp
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨hp.1, hp.2, rfl, rfl⟩

lemma step_crash {p : P}
    (h : (alg w t v₀).step C (.crash p) = some (C', ℓ)) :
    p ∉ C.crashed ∧ ℓ = none ∧ C' = ⟨C.loc, C.net, C.sent, insert p C.crashed⟩ := by
  simp only [Protocol.step] at h
  split_ifs at h with hp
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨hp, rfl, rfl⟩

lemma step_skip (h : (alg w t v₀).step C .skip = some (C', ℓ)) : C' = C ∧ ℓ = none := by
  simp only [Protocol.step, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-! ## Local transitions -/

lemma invoke_write {p : P} {v : V} {l l' : Loc P V} {out : Multiset (P × Msg V)}
    (h : invoke w p (.write v) l = some (l', out)) :
    p = w ∧ l.phase = .idle ∧
      l' = { l with hist := Function.update l.hist (l.ws p + 1) v,
                    ws := Function.update l.ws p (l.ws p + 1), phase := .w3 (l.ws p + 1) } ∧
      out = sendTo (fun j => Function.update l.ws p (l.ws p + 1) j = l.ws p + 1 - 1)
        (.write (par (l.ws p + 1)) v) := by
  unfold invoke at h
  split at h
  · rename_i v' hph
    simp only [RWOp.write.injEq] at *
    split_ifs at h with hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    subst hp
    refine ⟨rfl, hph, ?_, ?_⟩ <;> simp_all
  · simp at *
  · simp at h

lemma invoke_read {p : P} {l l' : Loc P V} {out : Multiset (P × Msg V)}
    (h : invoke w p .read l = some (l', out)) :
    p ≠ w ∧ l.phase = .idle ∧
      l' = { l with rs := Function.update l.rs p (l.rs p + 1), phase := .r7 (l.rs p + 1) } ∧
      out = sendTo (fun j => j ≠ p) .read := by
  unfold invoke at h
  split at h
  · simp at *
  · rename_i hph
    split_ifs at h with hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hp, hph, rfl, rfl⟩
  · simp at h

variable {q : ℕ}

lemma internal_wret {p : P} {l l' : Loc P V} {out : Multiset (P × Msg V)} {r : Option V}
    (h : internal q p .wret l = some (l', out, r)) :
    ∃ wsn, l.phase = .w3 wsn ∧ q ≤ count (fun j => l.ws j = wsn) ∧
      l' = { l with phase := .idle } ∧ out = 0 ∧ r = some (l.hist wsn) := by
  obtain ⟨hist, ws, rs, ph, tasks⟩ := l
  cases ph <;> simp [internal] at h
  obtain ⟨hq, rfl, rfl, rfl⟩ := h
  exact ⟨_, rfl, hq, rfl, rfl, rfl⟩

lemma internal_r8 {p : P} {l l' : Loc P V} {out : Multiset (P × Msg V)} {r : Option V}
    (h : internal q p .r8 l = some (l', out, r)) :
    ∃ rsn, l.phase = .r7 rsn ∧ q ≤ count (fun j => l.rs j = rsn) ∧
      l' = { l with phase := .r9 (l.ws p) } ∧ out = 0 ∧ r = none := by
  obtain ⟨hist, ws, rs, ph, tasks⟩ := l
  cases ph <;> simp [internal] at h
  obtain ⟨hq, rfl, rfl, rfl⟩ := h
  exact ⟨_, rfl, hq, rfl, rfl, rfl⟩

lemma internal_rret {p : P} {l l' : Loc P V} {out : Multiset (P × Msg V)} {r : Option V}
    (h : internal q p .rret l = some (l', out, r)) :
    ∃ sn, l.phase = .r9 sn ∧ q ≤ count (fun j => sn ≤ l.ws j) ∧
      l' = { l with phase := .idle } ∧ out = 0 ∧ r = some (l.hist sn) := by
  obtain ⟨hist, ws, rs, ph, tasks⟩ := l
  cases ph <;> simp [internal] at h
  obtain ⟨hq, rfl, rfl, rfl⟩ := h
  exact ⟨_, rfl, hq, rfl, rfl, rfl⟩

lemma internal_proceed {p j : P} {sn : ℕ} {l l' : Loc P V} {out : Multiset (P × Msg V)}
    {r : Option V} (h : internal q p (.proceed j sn) l = some (l', out, r)) :
    (j, sn) ∈ l.tasks ∧ sn ≤ l.ws j ∧ l' = { l with tasks := l.tasks.erase (j, sn) } ∧
      out = {(j, .proceed)} ∧ r = none := by
  obtain ⟨hist, ws, rs, ph, tasks⟩ := l
  cases ph <;> simp [internal] at h <;>
  · obtain ⟨⟨h1, h2⟩, rfl, rfl, rfl⟩ := h
    exact ⟨h1, h2, rfl, rfl, rfl⟩

lemma receive_write {p src : P} {b : Bool} {v : V} {l l' : Loc P V}
    {out : Multiset (P × Msg V)} {r : Option V}
    (h : receive p src (.write b v) l = some (l', out, r)) :
    b = par (l.ws src + 1) ∧ r = none ∧
      ((l.ws src + 1 = l.ws p + 1 ∧
          l' = { l with hist := Function.update l.hist (l.ws src + 1) v,
                        ws := Function.update (Function.update l.ws p (l.ws src + 1)) src
                          (l.ws src + 1) } ∧
          out = sendTo (fun ℓ => Function.update l.ws p (l.ws src + 1) ℓ = l.ws src + 1 - 1)
            (.write (par (l.ws src + 1)) v)) ∨
       (l.ws src + 1 < l.ws p ∧
          l' = { l with ws := Function.update l.ws src (l.ws src + 1) } ∧
          out = {(src, .write (par (l.ws src + 1 + 1)) (l.hist (l.ws src + 1 + 1)))}) ∨
       (l.ws src + 1 = l.ws p ∧
          l' = { l with ws := Function.update l.ws src (l.ws src + 1) } ∧ out = 0) ∨
       (l.ws p + 1 < l.ws src + 1)) := by
  unfold receive at h
  simp only at h
  split_ifs at h with hb h1 h2
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hb, rfl, Or.inl ⟨h1, rfl, rfl⟩⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨hb, rfl, Or.inr (Or.inl ⟨h2, rfl, rfl⟩)⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨hb, rfl, ?_⟩
    by_cases h3 : l.ws src + 1 = l.ws p
    · exact Or.inr (Or.inr (Or.inl ⟨h3, rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (by omega)))

lemma receive_read {p src : P} {l l' : Loc P V} {out : Multiset (P × Msg V)} {r : Option V}
    (h : receive p src .read l = some (l', out, r)) :
    l' = { l with tasks := l.tasks + {(src, l.ws p)} } ∧ out = 0 ∧ r = none := by
  unfold receive at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

lemma receive_proceed {p src : P} {l l' : Loc P V} {out : Multiset (P × Msg V)}
    {r : Option V} (h : receive p src .proceed l = some (l', out, r)) :
    l' = { l with rs := Function.update l.rs src (l.rs src + 1) } ∧ out = 0 ∧ r = none := by
  unfold receive at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

end Podc.TwoBit
