import Papers.PODC2021.TrustedHardwareUnidirectional.Claim41
import Papers.PODC2021.TrustedHardwareUnidirectional.SWMR
import Papers.PODC2021.TrustedHardwareUnidirectional.TrInc
import Papers.PODC2021.TrustedHardwareUnidirectional.Alg3
import Papers.PODC2021.TrustedHardwareUnidirectional.AppendixRB

/-!
# Ben-David–Nayak, *Classifying Trusted Hardware via Unidirectional Communication* (PODC 2021 BA)

Main results of the formalization (see `README.md`):

* `Podc.TrustedHW.claim_4_1_false`: the Claim of §4.1 ("SRB cannot implement unidirectionality
  for `n > 2f`, `f > 1`") is **false**; `Podc.TrustedHW.srb_implements_unidirectional`: SRB
  implements unidirectional rounds for every `n > 2f` (echo protocol,
  `Podc.TrustedHW.Echo.echoProtocol_implements`).
* `Podc.TrustedHW.SWMR.swmr_implements`: Claim of §3.2 (SWMR objects implement unidirectional
  rounds, any number of Byzantine processes).
* `Podc.TrustedHW.TrInc.*`: Theorem 1 (SRB implements the TrInc interface; eventual version).
* `Podc.TrustedHW.Alg3.agreement`, `Podc.TrustedHW.Alg3.l2_signed`,
  `Podc.TrustedHW.Alg3.validity_core`: safety core of the Claim of §4.2 (Lemmas 2–4) with the
  conflict check of the text; `Podc.TrustedHW.Alg3.pseudo_disagreement`: Algorithm 3 as written
  (without the check) violates agreement.
* `Podc.TrustedHW.AppendixRB.appendix_claim`: Claim of Appendix A (`f = 1`, `n ≥ 3`).
-/
