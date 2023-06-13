import Mathlib.Topology.Homotopy.Path
open Set

variable {X : Type _} [TopologicalSpace X] (x₀ : X) {x₁ : X }
-- def baseSet : TopologicalSpace X 

#check X

def coverSet :=
  Σ x₁ : X , Path.Homotopic.Quotient x₀ x₁

#check coverSet
#synth TopologicalSpace (Path x₀ x₁)

#synth TopologicalSpace (coverSet x₀)

example : IsOpen (univ : Cover) := 
  isOpen_univ




-- Hybrid approach

-- Construct Hatcher's version of the universal cover
-- Then show that the topology it has is equivalent to the one described in Bourbaki 
-- by taking the quotient of the path space of X (equipped with the compact open topology) 
-- with repsect to homotopy equivalence rel boundary.

-- I.e.  need to show that Hatcher's basis generates the compact-open topology quotient.

-- 










#exit


Sigma 