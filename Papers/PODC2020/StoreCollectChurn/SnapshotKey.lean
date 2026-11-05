import Papers.PODC2020.StoreCollectChurn.SnapshotOrder

/-!
# The linearization order of Section 6.2

Scans are ordered by their vectors (a chain by Lemma 11), ties by completion; each update `U`
is placed immediately before the first scan that sees it (`mU U` = the size of the vector of the
first scan that sees `U`, `⊤` if none), updates placed at the same point by invocation order.
This is encoded by the key `key x : ℕ∞ ×ₗ ℕ`.
-/

namespace Podc.StoreCollectChurn.Snap

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P V : Type} [DecidableEq P]

variable (E : List (Ev P V))

/-- The nodes that take steps in `E`. -/
def nodes : Finset P := (E.map Ev.proc).toFinset

/-- Size of the vector of a scan. -/
noncomputable def tot (x : OpId P) : ℕ := ∑ r ∈ nodes E, vec E x r

/-- The scan `S` sees the update `U`. -/
def Obs (S U : OpId P) : Prop := ScanOK E S ∧ kU E U ≤ vec E S U.1

open Classical in
/-- Where the update `U` is placed: the size of the first scan that sees it. -/
noncomputable def mU (U : OpId P) : ℕ∞ :=
  if h : ∃ S, Obs E S U then
    ((Nat.find (⟨_, h.choose, h.choose_spec, rfl⟩ : ∃ n, ∃ S, Obs E S U ∧ tot E S = n) : ℕ) : ℕ∞)
  else ⊤

open Classical in
/-- The linearization key. -/
noncomputable def key (x : OpId P) : ℕ∞ ×ₗ ℕ :=
  if opOf (hist E) x = some .scan then toLex ((tot E x : ℕ∞), E.length + 1 + retPos E x)
  else toLex (mU E x, invPos E x)

/-- An update that some store reflects (in particular every completed update). -/
def Vis (x : OpId P) : Prop :=
  (∃ v, opOf (hist E) x = some (.update x.1 v)) ∧ ∃ a y, StE E a x.1 y ∧ kU E x ≤ y.usqno

/-- The operations of the linearization. -/
def OSet : Set (OpId P) := {x | Invoked (hist E) x ∧ (ScanOK E x ∨ Vis E x)}

variable {E}

lemma invPos_lt (x : OpId P) : invPos E x < E.length + 1 := by
  classical
  unfold invPos
  split_ifs with h
  · have := (Nat.find_spec h).lt_length; omega
  · omega

lemma mU_le {S U : OpId P} (h : Obs E S U) : mU E U ≤ tot E S := by
  classical
  have hex : ∃ S, Obs E S U := ⟨S, h⟩
  simp only [mU, dif_pos hex]
  have := Nat.find_min' (⟨_, hex.choose, hex.choose_spec, rfl⟩ : ∃ n, ∃ S, Obs E S U ∧ tot E S = n)
    (m := tot E S) ⟨S, h, rfl⟩
  exact_mod_cast this

lemma mU_spec {U : OpId P} (h : mU E U ≠ ⊤) : ∃ S, Obs E S U ∧ mU E U = tot E S := by
  classical
  by_cases hex : ∃ S, Obs E S U
  · obtain ⟨S, hS, hS2⟩ := Nat.find_spec
      (⟨_, hex.choose, hex.choose_spec, rfl⟩ : ∃ n, ∃ S, Obs E S U ∧ tot E S = n)
    refine ⟨S, hS, ?_⟩
    simp only [mU, dif_pos hex]
    exact_mod_cast hS2.symm
  · exfalso; apply h; simp only [mU, dif_neg hex]

lemma key_scan {x : OpId P} (h : opOf (hist E) x = some .scan) :
    key E x = toLex ((tot E x : ℕ∞), E.length + 1 + retPos E x) := by
  classical
  simp [key, h]

lemma key_upd {x : OpId P} (h : opOf (hist E) x ≠ some .scan) :
    key E x = toLex (mU E x, invPos E x) := by
  classical
  simp [key, h]

lemma mem_OSet_scan {x : OpId P} (hx : x ∈ OSet E) (h : opOf (hist E) x = some .scan) :
    ScanOK E x := by
  rcases hx.2 with h' | ⟨⟨v, hv⟩, -⟩
  · exact h'
  · rw [hv] at h; cases h

variable {pk : Pick P V} (hrun : run pk E ≠ none) (hreg : Regular (scSched E))
include hrun hreg

lemma vec_eq_zero {x : OpId P} (hx : ScanOK E x) {r : P} (hr : r ∉ nodes E) : vec E x r = 0 := by
  obtain ⟨d, ⟨-, b, -⟩, hd⟩ := vec_spec hrun hreg hx
  rw [(hd r).2]
  rcases hW : d.W₂ r with _ | y
  · rfl
  obtain ⟨a, -, ha, -⟩ := reg1_some hreg b hW
  exfalso; apply hr
  have haL : a < E.length := by
    by_contra h'; rw [StE, List.getElem?_eq_none (by omega)] at ha; cases ha
  simp only [nodes, List.mem_toFinset, List.mem_map]
  refine ⟨E[a], List.getElem_mem haL, ?_⟩
  rw [StE, List.getElem?_eq_getElem haL] at ha
  rw [Option.some.inj ha]; rfl

lemma tot_le {x y : OpId P} (h : vec E x ≤ vec E y) : tot E x ≤ tot E y :=
  Finset.sum_le_sum fun r _ => h r

lemma tot_lt {x y : OpId P} (hy : ScanOK E y) (h : vec E x ≤ vec E y) {r : P}
    (hr : vec E x r < vec E y r) : tot E x < tot E y := by
  have hrn : r ∈ nodes E := by
    by_contra hc; rw [vec_eq_zero hrun hreg hy hc] at hr; omega
  exact Finset.sum_lt_sum (fun r _ => h r) ⟨r, hrn, hr⟩

lemma vec_le_of_tot_le {x y : OpId P} (hx : ScanOK E x) (hy : ScanOK E y)
    (h : tot E x ≤ tot E y) : vec E x ≤ vec E y := by
  rcases vec_total hrun hreg hx hy with h1 | h1
  · exact h1
  · by_cases hlt : ∃ r, vec E y r < vec E x r
    · obtain ⟨r, hr⟩ := hlt
      exact absurd (tot_lt hrun hreg hx h1 hr) (not_lt.2 h)
    · push_neg at hlt; exact hlt

/-- An update placed before a scan is seen by it. -/
lemma obs_of_key_lt {U S : OpId P} (hU : opOf (hist E) U ≠ some .scan) (hS : ScanOK E S)
    (h : key E U < key E S) : kU E U ≤ vec E S U.1 := by
  rw [key_upd hU, key_scan hS.2, Prod.Lex.toLex_lt_toLex'] at h
  have h1 : mU E U ≤ tot E S := h.1
  have hne : mU E U ≠ ⊤ := ne_top_of_le_ne_top (by simp) h1
  obtain ⟨S0, ⟨hS0, hk⟩, heq⟩ := mU_spec hne
  rw [heq] at h1
  exact hk.trans (vec_le_of_tot_le hrun hreg hS0 hS (by exact_mod_cast h1) U.1)

/-- An update seen by a scan is placed before it. -/
lemma key_lt_of_obs {U S : OpId P} (hU : opOf (hist E) U ≠ some .scan) (h : Obs E S U) :
    key E U < key E S := by
  rw [key_upd hU, key_scan h.1.2, Prod.Lex.toLex_lt_toLex']
  refine ⟨mU_le h, fun _ => ?_⟩
  have := invPos_lt (E := E) U
  simp only; omega

lemma invPos_lt_retPos {x : OpId P} (hc : Completed (hist E) x) : invPos E x < retPos E x := by
  obtain ⟨h, k', r, hi, hk, hlt, -⟩ := retFact_of_completed hrun hreg hc
  rw [invAt_invPos hi, retAt_retPos hk]; exact hlt

lemma upd_of_invoked {x : OpId P} (hx : Invoked (hist E) x) (hns : opOf (hist E) x ≠ some .scan) :
    ∃ h v, InvAt E x h ∧ E[h]? = some (.hinv x.1 (.update v)) := by
  obtain ⟨h, o, hh, hi⟩ := invoked_iff.1 hx
  rcases o with _ | v
  · exact absurd (opOf_of_invAt hh hi) hns
  · exact ⟨h, v, ⟨_, hh, hi⟩, hh⟩

/-- **Real-time order is respected by the keys.** -/
lemma key_lt_of_precedes {a b : OpId P} (hp : Precedes (hist E) a b) (hb : b ∈ OSet E) :
    key E a < key E b := by
  have ha : Completed (hist E) a := hp.completed
  obtain ⟨ka, hka⟩ := completed_iff.1 ha
  obtain ⟨kb, hkb⟩ := invoked_iff.1 hb.1
  have hab := precedes_pos hp hka hkb
  have hia := invPos_lt_retPos hrun hreg ha
  rw [retAt_retPos hka] at hia
  by_cases has : opOf (hist E) a = some .scan <;> by_cases hbs : opOf (hist E) b = some .scan
  · have hb' := mem_OSet_scan hb hbs
    have hv := vec_mono_of_precedes hrun hreg ⟨ha, has⟩ hb' hp
    have hib := invPos_lt_retPos hrun hreg hb'.1
    rw [invAt_invPos hkb] at hib
    rw [key_scan has, key_scan hbs, Prod.Lex.toLex_lt_toLex']
    refine ⟨?_, fun _ => ?_⟩
    · show ((tot E a : ℕ) : ℕ∞) ≤ (tot E b : ℕ∞)
      exact_mod_cast tot_le hrun hreg hv
    · rw [retAt_retPos hka]; simp only; omega
  · obtain ⟨h, v, hi, hh⟩ := upd_of_invoked hrun hreg hb.1 hbs
    have hlt := vec_lt_kU_of_precedes hrun hreg ⟨ha, has⟩ hi hh hp
    rw [key_scan has, key_upd hbs, Prod.Lex.toLex_lt_toLex']
    suffices htot : (tot E a : ℕ∞) < mU E b from ⟨htot.le, fun he => absurd he htot.ne⟩
    by_cases htop : mU E b = ⊤
    · rw [htop]; exact ENat.coe_lt_top _
    obtain ⟨S0, ⟨hS0, hk⟩, heq⟩ := mU_spec htop
    rw [heq]
    rcases vec_total hrun hreg ⟨ha, has⟩ hS0 with h1 | h1
    · have : vec E a b.1 < vec E S0 b.1 := by omega
      exact_mod_cast tot_lt hrun hreg hS0 h1 this
    · have : vec E S0 b.1 ≤ vec E a b.1 := h1 b.1
      omega
  · have hb' := mem_OSet_scan hb hbs
    exact key_lt_of_obs hrun hreg has ⟨hb', kU_le_vec_of_precedes hrun hreg ha has hb' hp⟩
  · obtain ⟨h, v, hi, hh⟩ := upd_of_invoked hrun hreg hb.1 hbs
    rw [key_upd has, key_upd hbs, Prod.Lex.toLex_lt_toLex']
    refine ⟨?_, fun _ => ?_⟩
    · by_cases htop : mU E b = ⊤
      · rw [htop]; exact le_top
      obtain ⟨S0, ⟨hS0, hk⟩, heq⟩ := mU_spec htop
      rw [heq]
      exact mU_le ⟨hS0, kU_le_vec_of_precedes_upd hrun hreg ha has hi hh hS0 hp hk⟩
    · rw [invAt_invPos hkb]; omega

/-- Keys are injective on the operations of the linearization. -/
lemma key_inj {x y : OpId P} (hx : x ∈ OSet E) (hy : y ∈ OSet E) (h : key E x = key E y) :
    x = y := by
  by_cases hxs : opOf (hist E) x = some .scan <;> by_cases hys : opOf (hist E) y = some .scan
  · rw [key_scan hxs, key_scan hys] at h
    have h2 := congrArg (fun z => (ofLex z).2) h
    simp only [ofLex_toLex] at h2
    obtain ⟨kx, hkx⟩ := completed_iff.1 (mem_OSet_scan hx hxs).1
    obtain ⟨ky, hky⟩ := completed_iff.1 (mem_OSet_scan hy hys).1
    rw [retAt_retPos hkx, retAt_retPos hky] at h2
    exact hkx.inj (by rwa [show kx = ky by omega])
  · rw [key_scan hxs, key_upd hys] at h
    have h2 := congrArg (fun z => (ofLex z).2) h
    simp only [ofLex_toLex] at h2
    have := invPos_lt (E := E) y; omega
  · rw [key_upd hxs, key_scan hys] at h
    have h2 := congrArg (fun z => (ofLex z).2) h
    simp only [ofLex_toLex] at h2
    have := invPos_lt (E := E) x; omega
  · rw [key_upd hxs, key_upd hys] at h
    have h2 := congrArg (fun z => (ofLex z).2) h
    simp only [ofLex_toLex] at h2
    obtain ⟨kx, hkx⟩ := invoked_iff.1 hx.1
    obtain ⟨ky, hky⟩ := invoked_iff.1 hy.1
    rw [invAt_invPos hkx, invAt_invPos hky] at h2
    exact hkx.inj (by rwa [h2])

end Podc.StoreCollectChurn.Snap
