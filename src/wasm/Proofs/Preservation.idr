import Proofs.Propositions

import Execution.JankInterp
import Execution.Runtime
import Validation.PatternValidator
import Structure.Types

preservation : OneStep i j -> HasType i t -> HasType j t
