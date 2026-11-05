import Papers.PODC2019.RMESubLogBoth.InvRepair2
import Papers.PODC2019.RMESubLogBoth.InvSteps

/-!
# The invariant holds in every reachable configuration
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

theorem inv_step {c c' : Cfg k} (hI : Inv c) {p : Fin k} (h : Step c p c') : Inv c' := by
  cases h with
  | l10_nil h hn => exact inv_step_l10_nil hI p h hn
  | l10_some h x hn => exact inv_step_l10_some hI p h x hn
  | l11 h => exact inv_step_l11 hI p h
  | l13 x h => exact inv_step_l13 hI p x h
  | l14 x m h => exact inv_step_l14 hI p x m h
  | l15 x m h => exact inv_step_l15 hI p x m h
  | l18 x h => exact inv_step_l18 hI p x h
  | l18w x h => exact inv_step_l18w hI p x h
  | l19 x h => exact inv_step_l19 hI p x h
  | l22a x h => exact inv_step_l22a hI p x h
  | l22b h => exact inv_step_l22b hI p h
  | l23 x v h => exact inv_step_l23 hI p x v h
  | l24_acq x v h hl => exact inv_step_l24_acq hI p x v h hl
  | l24_wait x v h q hl hq => exact inv_step_l24_wait hI p x v h q hl hq
  | l30 x v h => exact inv_step_l30 hI p x v h
  | l31 x h => exact inv_step_l31 hI p x h
  | l33 x tl V E i h hi => exact inv_step_l33 hI p x tl V E i h hi
  | l33_end x tl V E i h hi => exact inv_step_l33_end hI p x tl V E i h hi
  | l35 x tl V E i a h => exact inv_step_l35 hI p x tl V E i a h
  | l36 x tl V E i a h => exact inv_step_l36 hI p x tl V E i a h
  | l39 x tl V E h mpath hm tpath ht => exact inv_step_l39 hI p x tl V E h mpath hm tpath ht
  | l42_next x tl V E mpath tpath hpath done h σ hσ _ =>
    exact inv_step_l42_next hI p x tl V E mpath tpath hpath done h σ hσ
  | l42_end x tl V E mpath tpath hpath done h hall =>
    exact inv_step_l42_end hI p x tl V E mpath tpath hpath done h hall
  | l43 x tl V E mpath tpath hpath done σ h =>
    exact inv_step_l43 hI p x tl V E mpath tpath hpath done σ h
  | l44 x tl V E mpath tpath hpath done σ h =>
    exact inv_step_l44 hI p x tl V E mpath tpath hpath done σ h
  | l46_none x tl V E mpath hpath h => exact inv_step_l46_none hI p x tl V E mpath hpath h
  | l46_some x tl V E mpath τ hpath h =>
    split_ifs with hio
    · exact inv_step_l46_fas hI p x tl V E mpath τ hpath h hio
    · exact inv_step_l46_attach hI p x tl V E mpath τ hpath h (by simpa using hio)
  | l47 x s h => exact inv_step_l47 hI p x s h
  | l49 x m h => exact inv_step_l49 hI p x m h
  | rx x v h => exact inv_step_rx hI p x v h
  | l25 x v h => exact inv_step_l25 hI p x v h
  | l26 x h => exact inv_step_l26 hI p x h
  | cs x h => exact inv_step_cs hI p x h
  | l28 x h => exact inv_step_l28 hI p x h
  | l29 h => exact inv_step_l29 hI p h

theorem inv_next {c c' : Cfg k} (hI : Inv c) {e : Ev k} (h : Next c e c') : Inv c' := by
  cases e with
  | step p => exact inv_step hI h
  | crash p => change c' = c.crash p at h; subst h; exact inv_crash hI p

/-- The invariant holds in every reachable configuration. -/
theorem inv_reach {c : Cfg k} (h : Reach c) : Inv c := by
  induction h with
  | init => exact inv_init
  | next e _ hn ih => exact inv_next ih hn

end Podc.RMESubLogBoth
