import Mathlib.Topology.Homotopy.Path
open Set

variable {X : Type _} [TopologicalSpace X] {x₀ x₁ : X }
-- def baseSet : TopologicalSpace X 

def Cover :=
  ⋃ x₁ ∈ X , {γ | γ ∈ Path.Homotopic.Quotient x₀ x₁}