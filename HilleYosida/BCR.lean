/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license.
-/

import HilleYosida.BCR.Common
import HilleYosida.BCR.d0
import HilleYosida.BCR.Existence
import HilleYosida.BCR.Uniqueness
import HilleYosida.BCR.General
import HilleYosida.BCR.SemigroupGroupDefs
import HilleYosida.BCR.FourierPD
import HilleYosida.BCR.SemigroupGroupExtension

/-! # BCR pillar — facade

Re-exports the BCR Theorem 4.1.13 (semigroup Bochner) material:
the d=0 building block, the existence/uniqueness split for general
d, the semigroup-group definitions, and the Fourier-PD/group
extension assembly. Prefer `import HilleYosida.BCR` over the
individual sub-modules. -/
