import Papers.PODC2023.PPDoubleExpThresholds.MachineToProtocolDefs

/-!
# Clean configurations (Appendix B.3)

A *clean* configuration `render r g` has `r q` register agents in state `q` and exactly one agent
`g X` for every pointer `X` (owner-respecting: `g X` belongs to `X`). The map `π` of the paper is
`π(C) = render C.reg (fun X => X^{C(X)}_none)`.

`clean_fires` describes all transitions enabled in a clean configuration (no `⟨elect⟩` transition
is enabled, every transition changes the agents of at most two pointers, or one pointer and moves
a register agent), and `clean_fire_pp`, `clean_fire_pr` construct steps between clean
configurations.
-/

set_option linter.unusedSectionVars false

namespace Podc.PPDoubleExpThresholds

open Cslib Cslib.PopulationProtocol Cslib.TransitionSystem

namespace M2P

variable {Q F : Type*} [Fintype Q] [Fintype F] [DecidableEq Q] [DecidableEq F]

/-- The register agents: `r q` agents in state `q`. -/
def regsM (r : Q → ℕ) : Multiset (St Q F) := ∑ q, Multiset.replicate (r q) (St.reg q)

/-- A clean configuration. -/
def render (r : Q → ℕ) (g : F → St Q F) : Multiset (St Q F) :=
  regsM r + Finset.univ.val.map g

/-- `g X` belongs to `X` for every pointer `X`. -/
def OwnerResp (g : F → St Q F) : Prop := ∀ X, (g X).owner = some X

/-- Moving one unit from register `a` to register `b` (as in `Machine.Exec.move`). -/
def mvR (r : Q → ℕ) (a b : Q) : Q → ℕ :=
  Function.update (Function.update r a (r a - 1)) b (Function.update r a (r a - 1) b + 1)

theorem count_regsM (r : Q → ℕ) (s : St Q F) :
    (regsM r).count s = match s with | .reg q => r q | _ => 0 := by
  simp only [regsM, Multiset.count_sum']
  cases s with
  | reg q =>
    rw [Finset.sum_eq_single q]
    · simp
    · intro b _ hb; simp [Multiset.count_replicate, hb]
    · simp
  | ptr X v s => simp [Multiset.count_replicate]
  | map X i => simp [Multiset.count_replicate]

theorem mem_regsM {r : Q → ℕ} {s : St Q F} : s ∈ regsM r ↔ ∃ q, s = .reg q ∧ 0 < r q := by
  rw [← Multiset.count_pos, count_regsM]
  cases s <;> simp

theorem mvR_apply (r : Q → ℕ) (a b q : Q) (ha : 0 < r a) :
    mvR r a b q + (if q = a then 1 else 0) = r q + (if q = b then 1 else 0) := by
  simp only [mvR, Function.update_apply]
  by_cases h1 : q = b <;> by_cases h2 : q = a <;> by_cases h3 : b = a <;> simp_all <;> omega

theorem regsM_mvR {r : Q → ℕ} {a : Q} (b : Q) (ha : 0 < r a) :
    regsM (F := F) (mvR r a b) + {.reg a} = regsM r + {.reg b} := by
  ext s
  simp only [Multiset.count_add, count_regsM, Multiset.count_singleton]
  cases s with
  | reg q =>
    have := mvR_apply r a b q ha
    simp only [St.reg.injEq]
    convert this using 2
  | ptr => simp
  | map => simp

theorem mvR_self {r : Q → ℕ} {a : Q} (ha : 0 < r a) : mvR r a a = r := by
  funext q
  have := mvR_apply r a a q ha
  omega

theorem map_update_add {α β : Type*} [Fintype α] [DecidableEq α] (g : α → β) (X : α) (a : β) :
    Finset.univ.val.map (Function.update g X a) + {g X} = Finset.univ.val.map g + {a} := by
  have hX : X ∈ (Finset.univ : Finset α).val := Finset.mem_univ X
  rw [← Multiset.cons_erase hX, Multiset.map_cons, Multiset.map_cons]
  have : (Finset.univ.val.erase X).map (Function.update g X a) =
      (Finset.univ.val.erase X).map g := by
    apply Multiset.map_congr rfl
    intro Y hY
    have : Y ≠ X := (Finset.univ.nodup.mem_erase_iff.1 hY).1
    simp [this]
  rw [this]
  simp only [Function.update_self, ← Multiset.singleton_add]
  abel

theorem mem_render {r : Q → ℕ} {g : F → St Q F} {s : St Q F} :
    s ∈ render r g ↔ (∃ q, s = .reg q ∧ 0 < r q) ∨ ∃ X, s = g X := by
  simp [render, mem_regsM, eq_comm]

theorem count_render_g {r : Q → ℕ} {g : F → St Q F} (hg : OwnerResp g) (X : F) :
    (render r g).count (g X) = 1 := by
  have h1 : (regsM (F := F) r).count (g X) = 0 := by
    rw [count_regsM]
    have := hg X
    revert this
    cases g X <;> simp
  rw [render, Multiset.count_add, h1, zero_add, Multiset.count_map]
  have : Finset.univ.filter (fun Y => g X = g Y) = {X} := by
    ext Y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have h2 := hg Y
      rw [← h, hg X] at h2
      exact (Option.some_injective _ h2).symm
    · rintro rfl; rfl
  have := congrArg (fun s : Finset F => Multiset.card s.val) this
  simpa using this

theorem pair_le_render {r : Q → ℕ} {g : F → St Q F} {X Y : F} (hXY : X ≠ Y) :
    ({g X, g Y} : Multiset (St Q F)) ≤ render r g := by
  have h1 : ({X, Y} : Multiset F) ≤ Finset.univ.val := by
    rw [Multiset.le_iff_subset (by simp [hXY])]
    intro Z _; exact Finset.mem_univ Z
  have := Multiset.map_le_map (f := g) h1
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton] at this
  rw [Multiset.insert_eq_cons]
  exact this.trans (Multiset.le_add_left _ _)

theorem pr_le_render {r : Q → ℕ} {g : F → St Q F} {X : F} {u : Q} (hu : 0 < r u) :
    ({g X, .reg u} : Multiset (St Q F)) ≤ render r g := by
  rw [Multiset.pair_comm, Multiset.insert_eq_cons, ← Multiset.singleton_add, render]
  refine add_le_add (Multiset.singleton_le.2 (mem_regsM.2 ⟨u, rfl, hu⟩)) ?_
  exact Multiset.singleton_le.2 (Multiset.mem_map_of_mem _ (Finset.mem_univ X))

theorem render_update2 (r : Q → ℕ) (g : F → St Q F) {X Y : F} (hXY : X ≠ Y) (a b : St Q F) :
    render r (Function.update (Function.update g X a) Y b) + {g X, g Y} =
      render r g + {a, b} := by
  have h1 := map_update_add (Function.update g X a) Y b
  have h2 := map_update_add g X a
  rw [Function.update_of_ne hXY.symm] at h1
  simp only [render, Multiset.insert_eq_cons, ← Multiset.singleton_add]
  calc regsM r + Finset.univ.val.map (Function.update (Function.update g X a) Y b) +
        ({g X} + {g Y})
      = regsM r + (Finset.univ.val.map (Function.update (Function.update g X a) Y b) + {g Y})
        + {g X} := by abel
    _ = regsM r + (Finset.univ.val.map (Function.update g X a) + {g X}) + {b} := by
        rw [h1]; abel
    _ = regsM r + Finset.univ.val.map g + ({a} + {b}) := by rw [h2]; abel

theorem render_update_mv (r : Q → ℕ) (g : F → St Q F) (X : F) {u : Q} (hu : 0 < r u)
    (a : St Q F) (u' : Q) :
    render (mvR r u u') (Function.update g X a) + {g X, .reg u} =
      render r g + {a, .reg u'} := by
  have h1 := regsM_mvR (F := F) u' hu
  have h2 := map_update_add g X a
  simp only [render, Multiset.insert_eq_cons, ← Multiset.singleton_add]
  calc regsM (mvR r u u') + Finset.univ.val.map (Function.update g X a) + ({g X} + {.reg u})
      = (regsM (mvR r u u') + {.reg u}) + (Finset.univ.val.map (Function.update g X a) + {g X})
        := by abel
    _ = regsM r + Finset.univ.val.map g + ({a} + {.reg u'}) := by rw [h1, h2]; abel

theorem clean_fire_pp {r : Q → ℕ} {g : F → St Q F} (t : Transition (St Q F)) {X Y : F}
    (hXY : X ≠ Y) (hp : t.p = g X) (hq : t.q = g Y) :
    t.Fires (render r g) (render r (Function.update (Function.update g X t.p') Y t.q')) := by
  rw [fires_iff_add]
  have hpre : t.pre = {g X, g Y} := by simp [Transition.pre, hp, hq]
  refine ⟨hpre ▸ pair_le_render hXY, ?_⟩
  rw [hpre, render_update2 r g hXY]; rfl

theorem clean_fire_pr {r : Q → ℕ} {g : F → St Q F} (t : Transition (St Q F)) {X : F} {u u' : Q}
    (hp : t.p = g X) (hq : t.q = .reg u) (hq' : t.q' = .reg u') (hu : 0 < r u) :
    t.Fires (render r g) (render (mvR r u u') (Function.update g X t.p')) := by
  rw [fires_iff_add]
  have hpre : t.pre = {g X, .reg u} := by simp [Transition.pre, hp, hq]
  refine ⟨hpre ▸ pr_le_render hu, ?_⟩
  rw [hpre, render_update_mv r g X hu, ← hq']; rfl

end M2P

namespace Machine

open M2P

variable {Q F : Type*} [Fintype Q] [Fintype F] [DecidableEq Q] [DecidableEq F]
variable (A : Machine Q F)

theorem Tr.shape {t : Transition (St Q F)} (ht : A.Tr t) :
    (∃ X, t.p.owner = some X) ∧ ∀ u, t.q = .reg u → ∃ u', t.q' = .reg u' := by
  cases ht <;> simp_all <;> (intro u h; subst h; simp_all)

/-- All transitions enabled in a clean configuration. -/
theorem clean_fires {r : Q → ℕ} {g : F → St Q F} (hg : OwnerResp g) {t : Transition (St Q F)}
    (ht : A.Tr t) {c' : Multiset (St Q F)} (hf : t.Fires (render r g) c') :
    ∃ X, t.p = g X ∧
      ((∃ Y, Y ≠ X ∧ t.q = g Y ∧ c' = render r (Function.update (Function.update g X t.p') Y t.q'))
      ∨ (∃ u u', t.q = .reg u ∧ t.q' = .reg u' ∧ 0 < r u ∧
          c' = render (mvR r u u') (Function.update g X t.p'))) := by
  obtain ⟨⟨X₀, hX₀⟩, hreg⟩ := Tr.shape A ht
  have hp : t.p ∈ render r g := Multiset.mem_of_le hf.1 (by simp [Transition.pre])
  have hq : t.q ∈ render r g := Multiset.mem_of_le hf.1 (by simp [Transition.pre])
  obtain ⟨X, hX⟩ : ∃ X, t.p = g X := by
    rcases mem_render.1 hp with ⟨q, hq, -⟩ | h
    · rw [hq] at hX₀; simp at hX₀
    · exact h
  refine ⟨X, hX, ?_⟩
  rcases mem_render.1 hq with ⟨u, hu, hpos⟩ | ⟨Y, hY⟩
  · obtain ⟨u', hu'⟩ := hreg u hu
    exact .inr ⟨u, u', hu, hu', hpos, fires_unique hf (clean_fire_pr t hX hu hu' hpos)⟩
  · by_cases hXY : Y = X
    · subst hXY
      exfalso
      have h2 := Multiset.count_le_of_le (t.p) hf.1
      rw [hX, count_render_g hg] at h2
      simp [Transition.pre, hX, hY] at h2
    · exact .inl ⟨Y, hXY, hY, fires_unique hf (clean_fire_pp t (Ne.symm hXY) hX hY)⟩

end Machine

end Podc.PPDoubleExpThresholds
