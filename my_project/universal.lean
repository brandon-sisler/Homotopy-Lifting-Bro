import Mathlib.Topology.Homotopy.Path
open Set

variable {X : Type _} [TopologicalSpace X] {x₀ x₁ : X }
-- def baseSet : TopologicalSpace X 

def Cover :=
  Σ x₁ : X , Path.Homotopic.Quotient x₀ x₁



#exit


Sigma 