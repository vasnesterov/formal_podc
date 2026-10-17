import Mathlib
import Podc.SharedMemory.Objects.FetchAdd
import Podc.SharedMemory.Objects.TestAndSet
import Podc.SharedMemory.Objects.MaxRegister
import Podc.SharedMemory.Objects.Snapshot

/-!
# Standard shared objects with consensus number 1 or 2 (compatibility module)

Re-exports the parts of the object catalog `Podc.SharedMemory.Objects.*` that used to be
defined here: `faaObj V`, `tasObj`, `rtasObj`, `mtasObj`, `rfaiObj`, `maxRegObj`, `snapObj n`
(with their operation types). New code should import the catalog modules directly.
-/
