import Papers.PODC2026.LockFreeLinearProbing.DefsCAS

/-!
# The CAS version (Algorithm 6) is not linearizable

A table of `m = 2` cells, both keys hashed to cell `0`, two processes:

* `p0` runs `insert(v)`: it writes its tentative copy into cell `0` (line 43) and starts its
  duplicate scan;
* `p1` runs `delete(v)`: it overwrites `p0`'s copy with `DELETED` (line 88) and returns `true`;
* `p1` then runs `insert(v)`: cell `0` holds `DELETED`, so it writes its tentative copy into
  cell `1` and validates it up to line 66;
* `p0`, whose copy is already deleted, continues its duplicate scan, reads `p1`'s copy in cell
  `1` (line 65) and **marks** it (line 116 — Algorithm 6 marks before checking its own cell,
  line 120);
* `p1`'s `CAS` to `⟨v, final⟩` (line 67) fails; line 69 tests the stale value read at line 66,
  and `del_copy` only resurrects `⟨v, revalidate⟩` (line 77), so `p1` tombstones its marked copy
  (line 80) and its `insert(v)` returns `false`.

`delete(v)` returned `true` before the second `insert(v)` was invoked, and the only other
`insert(v)` must precede that `delete`: no linearization exists (`cex_not_linearizable`).
-/

namespace Podc.LockFreeLinearProbing.CAS

open Cslib.SharedMemory

/-- Both keys are hashed to cell `0`. -/
def hh : ℕ → Fin 2 := fun _ => 0

/-- The CAS hash table with two cells and two processes. -/
abbrev Ic : Impl (dict ℕ) (MemC ℕ 2) (Fin 2) (LocC ℕ 2) := implC hh

instance : ∀ p o, Decidable (Ic.allowed p o) := fun _ _ => isTrue trivial

/-- Labels. -/
abbrev Lb := Label (Fin 2) (dict ℕ)

/-- `n` steps of process `p`. -/
abbrev taus (p : Fin 2) (n : ℕ) : List Lb := List.replicate n (.tau p)

/-- The counterexample execution (key `v = 1`). -/
def cex : List Lb :=
  [.inv 0 (.insert 1)] ++ taus 0 5 ++ [.inv 1 (.delete 1)] ++ taus 1 2 ++
    [.ret 1 (.ok true), .inv 1 (.insert 1)] ++ taus 1 6 ++ taus 0 1 ++ taus 1 3 ++ taus 0 1 ++
    taus 1 3 ++ [.ret 1 (.ok false)]

/-- `cex` is an execution of the CAS hash table. -/
theorem cex_valid : Ic.Valid cex :=
  Impl.valid_of_crun _ (by decide +kernel)

/-! ### No linearization -/

/-- Legality for `dictSpec` as a Boolean function (the post-state of a step is determined by the
pre-state, the operation and the response). -/
def legalB : (ℕ → Bool) → List (DOp ℕ × Res) → Bool
  | _, [] => true
  | s, (.insert _, .abort) :: l => legalB s l
  | s, (.insert v, .ok b) :: l => (b == !s v) && legalB (Function.update s v true) l
  | s, (.delete v, .ok b) :: l => (b == s v) && legalB (Function.update s v false) l
  | s, (.lookup v, .ok b) :: l => (b == s v) && legalB s l
  | _, (_, .abort) :: _ => false

lemma legal_imp_legalB (s : ℕ → Bool) (l : List (DOp ℕ × Res)) :
    (dictSpec ℕ).Legal s l → legalB s l = true := by
  induction l generalizing s with
  | nil => intro; rfl
  | cons a l ih =>
    obtain ⟨o, r⟩ := a
    rintro ⟨s', hst, hl⟩
    rcases hst with hst | ⟨v, rfl, rfl, rfl⟩
    · rcases o with v | v | v <;> rcases r with b | _ <;>
        simp only [dict] at hst <;>
        obtain ⟨rfl, rfl⟩ := hst <;> simp [legalB, ih _ hl]
    · simp only [legalB]; exact ih _ hl

/-- The candidate entries of a linearization of `cex`: the pending `insert` of `p0` with any
response, and the two completed operations of `p1` with their responses. -/
def cands : List (OpId (Fin 2) × (dict ℕ).Op × (dict ℕ).Resp) :=
  [((0, 0), DOp.insert 1, Res.ok true), ((0, 0), DOp.insert 1, Res.ok false),
    ((0, 0), DOp.insert 1, Res.abort), ((1, 0), DOp.delete 1, Res.ok true),
    ((1, 1), DOp.insert 1, Res.ok false)]

lemma cex_ops0 : opsOf cex 0 = [(DOp.insert 1 : (dict ℕ).Op)] := by rfl
lemma cex_ops1 : opsOf cex 1 = [(DOp.delete 1 : (dict ℕ).Op), DOp.insert 1] := by rfl
lemma cex_resps1 : respsOf cex 1 = [(Res.ok true : (dict ℕ).Resp), Res.ok false] := by rfl

lemma mem_cands {y : OpId (Fin 2) × (dict ℕ).Op × (dict ℕ).Resp}
    (hop : opOf cex y.1 = some y.2.1) (hr : ∀ r, respOf cex y.1 = some r → y.2.2 = r) :
    y ∈ cands := by
  obtain ⟨⟨p, k⟩, o, r⟩ := y
  simp only at hop hr
  have hp : p = 0 ∨ p = 1 := by fin_cases p <;> simp
  rcases hp with rfl | rfl
  · rw [opOf, cex_ops0] at hop
    rcases k with _ | k
    · have : some (DOp.insert 1 : (dict ℕ).Op) = some o := hop
      cases this
      rcases r with ⟨_ | _⟩ | _ <;> decide
    · have : (none : Option (dict ℕ).Op) = some o := hop
      cases this
  · rw [opOf, cex_ops1] at hop
    rcases k with _ | _ | k
    · have : some (DOp.delete 1 : (dict ℕ).Op) = some o := hop
      cases this
      have := hr (Res.ok true) (by rw [respOf, cex_resps1]; rfl); subst this; decide
    · have : some (DOp.insert 1 : (dict ℕ).Op) = some o := hop
      cases this
      have := hr (Res.ok false) (by rw [respOf, cex_resps1]; rfl); subst this; decide
    · have : (none : Option (dict ℕ).Op) = some o := hop
      cases this

/-- The finite check: no arrangement of the candidates containing the `delete` and the second
`insert`, in this order, is legal. -/
lemma check : ∀ L' ∈ cands.sublists.flatMap List.permutations',
    [((1 : Fin 2), 0), ((1 : Fin 2), 1)].isSublist (L'.map Prod.fst) = true →
    legalB (fun _ => false) (L'.map Prod.snd) = false := by
  decide +kernel

/-- **The CAS version of the hash table (Algorithm 6) is not linearizable**: the execution
`cex` has no linearization with respect to the dictionary specification (with `ABORT`). This
contradicts Theorem 1 of the paper for the CAS primitive. -/
theorem cex_not_linearizable : ¬ ∃ L, IsNLinearization (dictSpec ℕ) cex L := by
  rintro ⟨L, hL⟩
  have hsub : ∀ y ∈ L, y ∈ cands := fun y hy => mem_cands (hL.op_eq y hy) (hL.resp_eq y hy)
  have hnd : L.Nodup := hL.nodup.of_map _
  obtain ⟨t, htL, htc⟩ := hnd.subperm hsub
  have hmem : L ∈ cands.sublists.flatMap List.permutations' :=
    List.mem_flatMap.2 ⟨t, List.mem_sublists.2 htc, List.mem_permutations'.2 htL.symm⟩
  have hD : ((1 : Fin 2), 0) ∈ L.map Prod.fst :=
    hL.complete _ (by simp only [Completed, cex_resps1]; decide)
  have hI1 : ((1 : Fin 2), 1) ∈ L.map Prod.fst :=
    hL.complete _ (by simp only [Completed, cex_resps1]; decide)
  have hpre : Precedes cex ((1 : Fin 2), 0) ((1 : Fin 2), 1) :=
    ⟨cex.take 10, cex.drop 10, (List.take_append_drop 10 _).symm,
      by show 0 < (respsOf (cex.take 10) 1).length; decide,
      by show ¬ 1 < (opsOf (cex.take 10) 1).length; decide⟩
  have h1 := check L hmem (List.isSublist_iff_sublist.2 (hL.realtime _ _ hpre hI1))
  have h2 := legal_imp_legalB _ _ hL.legal
  change legalB (fun _ => false) _ = true at h2
  exact Bool.false_ne_true (h1.symm.trans h2)

/-- **Theorem 1 fails for the CAS version** (Algorithms 1–4 with Algorithm 6): some execution of
the CAS hash table (two processes, two cells) has no linearization. -/
theorem cas_not_linearizable :
    ∃ α, Ic.Valid α ∧ ¬ ∃ L, IsNLinearization (dictSpec ℕ) α L :=
  ⟨cex, cex_valid, cex_not_linearizable⟩

end Podc.LockFreeLinearProbing.CAS
