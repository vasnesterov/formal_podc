import Mathlib
import Podc.SharedMemory.Sequential

/-!
# Sequential executions are linearizable only if they are legal

The generic tools (`seqExec`, `LegalFrom`, `legalFromB`, `IsLinearization.legal_of_seqExec`,
`Impl.not_linearizable_of_seqExec`, `Impl.not_linearizable_of_resp`) now live in the shared
library module `Podc.SharedMemory.Sequential`.
-/
