import Mathlib
import Podc.SharedMemory.Objects.Window
import Podc.SharedMemory.Objects.Queue
import Podc.SharedMemory.ObjClasses.Basic

/-!
# Window registers, stacks, queues and classes of base objects (compatibility module)

Re-exports what used to be defined here: the objects `windowObj V w`, `stackObj V`,
`queueObj V` (now in `Podc.SharedMemory.Objects.Window` / `Podc.SharedMemory.Objects.Queue`)
and the classes `ObjSpec.CommuteAt`, `ObjSpec.OverwritesAt`, `ObjSpec.Interfering`,
`ObjSpec.WindowLike`, `StackRep`, `ObjSpec.StackLike` (now in
`Podc.SharedMemory.ObjClasses.Basic`). New code should import those modules, or
`Podc.SharedMemory.ObjClasses` for all object classes.
-/
