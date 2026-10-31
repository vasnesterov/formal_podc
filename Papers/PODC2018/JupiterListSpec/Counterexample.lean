import Papers.PODC2018.JupiterListSpec.JupiterMain
import Papers.PODC2018.JupiterListSpec.CJupiter

/-!
# Out-of-range positions break Jupiter (Section 2.3 + Figure A.1)

The paper lets users invoke `Ins(a, p)`/`Del(p)` with `p` larger than the list size ("we assume
an insertion/deletion at the end", Section 2.3) and the clients send the operation unchanged
(Algorithm B.5 / C.5); the OT functions of Figure A.1 compare the raw positions. With two
clients:

1. `c₀` inserts `x` at position 0; it reaches the server and `c₁`;
2. `c₀` invokes `Del(5)` on `[x]` (deletes the last element `x`), `c₁` invokes `Ins(b, 1)` on `[x]`
   (appends `b`);
3. the server processes `Del(5)` first, then `Ins(b, 1)` (transformed against `Del(5)`: `1 ≤ 5`,
   unchanged); `c₀` applies `Ins(b, 1)` to `[]` and gets `[b]`; `c₁` transforms `Del(5)` against
   its own `Ins(b, 1)`: `5 ≥ 1`, so `Del(6)`, which on `[x, b]` deletes the last element `b`;
4. both clients read: `c₀` reads `[b]`, `c₁` reads `[x]`, although both have seen all three updates.

This violates the convergence property (with visibility = happened-before), hence the weak list
specification, for Jupiter (`jupiter_raw_counterexample`) and for CJupiter
(`cjupiter_raw_counterexample`). The violation of `A_weak` does not depend on the choice of the
abstract execution: no well-formed abstract execution complying with the run is in `A_weak`
(`cjupiter_raw_not_weak_any`, `jupiter_raw_not_weak_any`), because `c₁`'s final `Read` misses
`c₁`'s own insertion of `b`. Normalising the positions at generation (`genOp`) fixes it.
-/

namespace Podc.JupiterListSpec

open Cfg

/-- The schedule of the counterexample. -/
def cexEvents : List (Ev 2) :=
  [.do 0 (.ins 0), .srv 0, .recv 1, .do 0 (.del 5), .do 1 (.ins 1), .srv 0, .srv 1, .recv 0,
    .recv 1, .do 0 .read, .do 1 .read]

/-- What the execution looks like: identifiers, signatures, returned lists and contexts of the
`do` events. -/
theorem cex_run :
    (run genRaw (jupiter 2) cexEvents).map (fun cfg => cfg.log.map fun r => (r.oid, r.sig, r.ret)) =
      some [((0, 0), .ins (0, 0) 0, [(0, 0)]), ((0, 1), .del (some (0, 0)) 5, []),
        ((1, 0), .ins (1, 0) 1, [(0, 0), (1, 0)]), ((0, 2), .read, [(1, 0)]),
        ((1, 1), .read, [(0, 0)])] := by
  decide

/-- The configuration reached by the counterexample. -/
def cexCfg : Cfg (jupiter 2) := (run genRaw (jupiter 2) cexEvents).get (by decide)

theorem cexCfg_run : run genRaw (jupiter 2) cexEvents = some cexCfg := by
  simp [cexCfg]

/-- A computable form of `vis`. -/
def visB {n : ℕ} {P : Proto n} (cfg : Cfg P) (i j : ℕ) : Bool :=
  decide (i < j) && match cfg.log[i]?, cfg.log[j]? with
    | some ri, some rj => decide (ri.oid ∈ rj.ctx)
    | _, _ => false

/-- A computable form of `IsUpdate`. -/
def updB {n : ℕ} {P : Proto n} (cfg : Cfg P) (j : ℕ) : Bool :=
  match cfg.log[j]? with
    | some r => decide (r.sig ≠ .read)
    | none => false

theorem vis_iff {n : ℕ} {P : Proto n} (cfg : Cfg P) (i j : ℕ) :
    (absExec cfg).vis i j ↔ visB cfg i j = true := by
  simp only [absExec, visB, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hij, ri, rj, hi, hj, hm⟩
    rw [hi, hj]; exact ⟨hij, by simpa using hm⟩
  · rintro ⟨hij, hm⟩
    revert hm
    cases hi : cfg.log[i]? <;> cases hj : cfg.log[j]? <;> simp
    exact fun hm => ⟨hij, hm⟩

theorem isUpdate_iff {n : ℕ} {P : Proto n} (cfg : Cfg P) (j : ℕ) :
    (absExec cfg).IsUpdate j ↔ updB cfg j = true := by
  simp only [AbsExec.IsUpdate, absExec, List.getElem?_map, updB]
  cases cfg.log[j]? <;> simp

/-- **Jupiter with the paper's out-of-range positions violates the convergence property**: the
two final `Read`s see the same three updates but return `[b]` and `[x]`. -/
theorem jupiter_raw_not_conv : ¬ (absExec cexCfg).Conv := by
  intro hc
  have hlen : cexCfg.log.length = 5 := by decide
  have h := hc 3 4 (by decide) (by decide) (by decide) (by decide) (by
    intro j hj
    rw [isUpdate_iff] at hj
    rw [vis_iff, vis_iff]
    rcases j with _ | _ | _ | _ | _ | j
    · decide
    · decide
    · decide
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
    · exfalso
      have : cexCfg.log[j + 5]? = none := by
        rw [List.getElem?_eq_none]; omega
      simp [updB, this] at hj)
  revert h
  decide

/-- Hence it violates the weak list specification (Theorems 11 and 18 fail for the paper's
literal model). -/
theorem jupiter_raw_not_weak : ¬ (absExec cexCfg).Weak :=
  fun hw => jupiter_raw_not_conv hw.conv

/-- The execution is a genuine execution of the protocol of the paper. -/
theorem jupiter_raw_counterexample :
    ∃ es cfg, run genRaw (jupiter 2) es = some cfg ∧ ¬ (absExec cfg).Weak ∧ ¬ (absExec cfg).Conv :=
  ⟨cexEvents, cexCfg, cexCfg_run, jupiter_raw_not_weak, jupiter_raw_not_conv⟩

/-- CJupiter with the paper's out-of-range positions diverges in the same way: `c₀` reads `[b]`,
`c₁` reads `[x]`. -/
theorem cex_run_cjupiter :
    (run genRaw (cjupiter 2) cexEvents).map
        (fun cfg => cfg.log.map fun r => (r.oid, r.sig, r.ret)) =
      some [((0, 0), .ins (0, 0) 0, [(0, 0)]), ((0, 1), .del (some (0, 0)) 5, []),
        ((1, 0), .ins (1, 0) 1, [(0, 0), (1, 0)]), ((0, 2), .read, [(1, 0)]),
        ((1, 1), .read, [(0, 0)])] := by
  decide

/-- The configuration reached by the counterexample under CJupiter. -/
def cexCfgC : Cfg (cjupiter 2) := (run genRaw (cjupiter 2) cexEvents).get (by decide)

theorem cexCfgC_run : run genRaw (cjupiter 2) cexEvents = some cexCfgC := by
  simp [cexCfgC]

/-- **CJupiter with the paper's out-of-range positions violates the convergence property**
(Theorem 11 fails for the literal model). -/
theorem cjupiter_raw_not_conv : ¬ (absExec cexCfgC).Conv := by
  intro hc
  have hlen : cexCfgC.log.length = 5 := by decide
  have h := hc 3 4 (by decide) (by decide) (by decide) (by decide) (by
    intro j hj
    rw [isUpdate_iff] at hj
    rw [vis_iff, vis_iff]
    rcases j with _ | _ | _ | _ | _ | j
    · decide
    · decide
    · decide
    · exact absurd hj (by decide)
    · exact absurd hj (by decide)
    · exfalso
      have : cexCfgC.log[j + 5]? = none := by
        rw [List.getElem?_eq_none]; omega
      simp [updB, this] at hj)
  revert h
  decide

/-- **Theorems 11 and 18 fail for the paper's literal model**: an execution of CJupiter (with the
user's positions sent unchanged) whose abstract execution is neither in `A_cp` nor in `A_weak`. -/
theorem cjupiter_raw_counterexample :
    ∃ es cfg, run genRaw (cjupiter 2) es = some cfg ∧ ¬ (absExec cfg).Weak ∧
      ¬ (absExec cfg).Conv :=
  ⟨cexEvents, cexCfgC, cexCfgC_run, fun hw => cjupiter_raw_not_conv hw.conv,
    cjupiter_raw_not_conv⟩

/-! ### Robustness: no choice of the abstract execution helps

The paper's `R ⊨ S` asks that every execution *complies with some* abstract execution in `S`
(the per-replica subsequences of `H` are the replica's `do` events; `vis` is any well-formed
visibility). The divergent execution violates `A_weak` for *every* such choice: `c₁`'s final
`Read` must see `c₁`'s own earlier `Ins(b, 1)` (per-replica order), nobody deletes `b`, yet it
returns `[x]`. -/

theorem exists_idx_of_filter_eq_pair {α : Type} {p : α → Bool} {l : List α} {a b : α}
    (h : l.filter p = [a, b]) :
    ∃ i j, ∃ (_ : i < j) (hj : j < l.length), l[i] = a ∧ l[j] = b := by
  have hs : [a, b].Sublist l := h ▸ List.filter_sublist
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.1 hs
  refine ⟨f ⟨0, by simp⟩, f ⟨1, by simp⟩, f.strictMono (Fin.mk_lt_mk.2 (by norm_num)),
    (f ⟨1, by simp⟩).2, ?_, ?_⟩
  · have := hf ⟨0, by simp⟩; simpa using this.symm
  · have := hf ⟨1, by simp⟩; simpa using this.symm

private theorem doEv_map_injective :
    Function.Injective (fun e : DoEv (Fin 2) (Oid 2) => (e.rep, e.sig, e.ret)) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- If the `do` events of an execution are those of the counterexample, then no abstract execution
complying with it is in `A_weak`. -/
theorem not_weak_of_cex_log {P : Proto 2} (cfg : Cfg P)
    (hlog : cfg.log.map (fun r => (r.oid.1, r.sig, r.ret)) =
      [((0 : Fin 2), Sig.ins ((0 : Fin 2), 0) 0, [((0 : Fin 2), 0)]),
        (0, Sig.del (some (0, 0)) 5, []), (1, Sig.ins (1, 0) 1, [(0, 0), (1, 0)]),
        (0, Sig.read, [(1, 0)]), (1, Sig.read, [(0, 0)])])
    (A : AbsExec (Fin 2) (Oid 2)) (hwf : A.WF)
    (hc : ∀ r, A.H.filter (fun e => decide (e.rep = r)) =
      (absExec cfg).H.filter (fun e => decide (e.rep = r))) : ¬ A.Weak := by
  have hH : (absExec cfg).H = [⟨0, .ins (0, 0) 0, [(0, 0)]⟩, ⟨0, .del (some (0, 0)) 5, []⟩,
      ⟨1, .ins (1, 0) 1, [(0, 0), (1, 0)]⟩, ⟨0, .read, [(1, 0)]⟩, ⟨1, .read, [(0, 0)]⟩] := by
    apply List.map_injective_iff.2 doEv_map_injective
    simpa [absExec, List.map_map, Function.comp_def] using hlog
  rintro ⟨lo, -, h1, -⟩
  have hf : A.H.filter (fun e => decide (e.rep = 1)) =
      [⟨1, .ins (1, 0) 1, [(0, 0), (1, 0)]⟩, ⟨1, .read, [(0, 0)]⟩] := by
    rw [hc, hH]; rfl
  obtain ⟨i, j, hij, hj, hi, hj'⟩ := exists_idx_of_filter_eq_pair hf
  have hv : A.vis i j := hwf.1 i j _ hj hij (by rw [hi, hj'])
  have key := ((h1 j hj).1 (1, 0)).2 ⟨⟨i, Or.inr hv, A.H[i], by simp, 1, by rw [hi]⟩, ?_⟩
  · rw [hj'] at key; simp at key
  · rintro ⟨k, -, e, he, k', hs⟩
    have heH : e ∈ A.H := List.mem_of_getElem? he
    have : e ∈ (absExec cfg).H := by
      have : e ∈ A.H.filter (fun e' => decide (e'.rep = e.rep)) :=
        List.mem_filter.2 ⟨heH, by simp⟩
      rw [hc] at this
      exact (List.mem_filter.1 this).1
    rw [hH] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl | rfl <;> simp at hs

/-- **Theorem 18 fails for the paper's literal model, for every choice of abstract execution**:
the divergent execution of CJupiter complies with no abstract execution in `A_weak`. -/
theorem cjupiter_raw_not_weak_any (A : AbsExec (Fin 2) (Oid 2)) (hwf : A.WF)
    (hc : ∀ r, A.H.filter (fun e => decide (e.rep = r)) =
      (absExec cexCfgC).H.filter (fun e => decide (e.rep = r))) : ¬ A.Weak :=
  not_weak_of_cex_log cexCfgC (by
    have h := congrArg (Option.map (List.map fun t : Oid 2 × Sig (Oid 2) × List (Oid 2) =>
      (t.1.1, t.2))) cex_run_cjupiter
    rw [cexCfgC_run] at h
    simpa [List.map_map, Function.comp_def] using h) A hwf hc

/-- The same for Jupiter (the conjecture of Attiya et al. fails for the literal model). -/
theorem jupiter_raw_not_weak_any (A : AbsExec (Fin 2) (Oid 2)) (hwf : A.WF)
    (hc : ∀ r, A.H.filter (fun e => decide (e.rep = r)) =
      (absExec cexCfg).H.filter (fun e => decide (e.rep = r))) : ¬ A.Weak :=
  not_weak_of_cex_log cexCfg (by
    have h := congrArg (Option.map (List.map fun t : Oid 2 × Sig (Oid 2) × List (Oid 2) =>
      (t.1.1, t.2))) cex_run
    rw [cexCfg_run] at h
    simpa [List.map_map, Function.comp_def] using h) A hwf hc

end Podc.JupiterListSpec
