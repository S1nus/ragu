import Ragu.Circuits.Endoscalar.GroupScale
import Ragu.Core

namespace Ragu.Instances.Endoscalar.GroupScale

@[reducible]
def p := Core.Primes.p

/-- Deserialize the flat 130-wire input: first 128 are endoscalar bits, last 2
are the curve point's `(x, y)` coordinates. -/
def deserializeInput (input : Vector (Expression (F p)) 130)
    : Var Circuits.Endoscalar.GroupScale.Input (F p) :=
  { bits := Vector.ofFn (fun (i : Fin 128) => input[i.val]'(by have := i.isLt; omega))
    pt := ⟨input[128], input[129]⟩ }

/-- Serialize the output point as a 2-wire vector. -/
def serializeOutput (output : Var Circuits.Point.Spec.Point (F p))
    : Vector (Expression (F p)) 2 :=
  #v[output.x, output.y]

def formal_instance : Core.Statements.FormalInstance where
  p
  deserializeInput
  serializeOutput

  reimplementation :=
    (Circuits.Endoscalar.GroupScale.circuit
      Circuits.Point.Spec.EpAffineParams).isGeneralFormalCircuit.toWithHint

end Ragu.Instances.Endoscalar.GroupScale
