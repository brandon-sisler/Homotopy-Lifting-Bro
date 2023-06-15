--import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.IsLocallyHomeomorph
--import Mathlib.Topology.FiberBundle.basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Topology.Covering
--import Mathlib.Topology.basic

set_option maxHeartbeats 0

open Set Filter Topology




















variable (Y:Type _)  [TopologicalSpace Y](S : Set Y)

 


/- Lemma 1 stating that a set S ⊆ Y is clopen in Y ↔ ∀ y ∈ Y ∃ nbhd U_y of y 
such that U_y ∩ S is clopen in U_y -/

lemma ClopenIffNbhdClopen (Y: Type _) [TopologicalSpace Y](S : Set Y) :
 (∀ y :  Y, ∃ U: Set Y,  U ∈ 𝓝 y) ↔ IsClopen S := by sorry



/- Lemma 1 proof -/



/- Lemma 2 stating that if f, g : X → Y are continuous and Y is a discrete topological
space, then {x ∈ X ∣ f(x) = g(x)} is clopen in X -/

lemma EquilizerOfDiscreteIsClopen (X Y: Type _) [TopologicalSpace X] [TopologicalSpace Y]
  [DiscreteTopology Y] (f g:ContinuousMap X Y)  : 
  IsClopen {x : X | f x = g x} := by sorry
  

/- Lemma 2 proof -/



/- Lemma 3 stating that if a clopen set S ⊆ Y intersects with all the connected components of Y, then S = Y -/

#check connectedComponent
#check IsClopen.connectedComponent_subset

lemma ClopenInterConnectedCompUniv (Y: Type _)[TopologicalSpace Y](S: Set Y)(hS: IsClopen S)
(h: ∀x :Y, ∃ y∈ connectedComponent x, y∈ S): S=Set.univ := by


/- Lemma 3 proof -/
  ext z                   
  constructor
  · exact fun _ => trivial
  intro 
  specialize h z
  rcases h with ⟨y,hy, yS⟩ 
  have h1:= IsClopen.connectedComponent_subset hS yS
  have h2 : z∈ connectedComponent y := by
    rw [← connectedComponent_eq_iff_mem]
    exact connectedComponent_eq hy
  apply h1
  exact h2



--- Statement of the Theorem ---


theorem UniquenessOfHomotopyLifting (Y X E: Type _) 
[TopologicalSpace Y][TopologicalSpace X][TopologicalSpace E]
(f:ContinuousMap E X)(hf: IsCoveringMap f)
(H₁ H₂ : ContinuousMap Y E)(h: f ∘ H₁ = f ∘ H₂)
(hC : ∀ x : Y, ∃ y ∈ connectedComponent x, H₁ y = H₂ y) : H₁ = H₂  := by 

  

/- Define S := {y ∈ Y ∣ H₁(y) = H₂(y)} -/
  let S:= {y:Y | H₁ y = H₂ y}
  

/- S is clopen proof Part 1 : by Lemma 1 it suffices to prove that U_y ∩ S is
clopen in U_y (where for y ∈ Y, F(y) ∈ X has evenly covered nbhd V_y by defn
of covering and U_y := F^{-1}(V_y)) -/

  have ClopenS : IsClopen S := by
   rw [← ClopenIffNbhdClopen]
   sorry
   



/- S is clopen proof Part 2(a) : U_y ∩ S = {z ∈ U_y ∣ H₁(z) = H₂(z)} -/



/- S is clopen proof Part 2(b) : ∃ discrete topological space D such that 
f⁻¹(V_y) ≅ V_y × D := by defn of covering -/



/- S is clopen proof Part 2(c) : {z ∈ U_y ∣ (proj_D ∘ H₁)(z) = (proj_D ∘ H₂)(z)} is clopen in U_y := 
by Lemma 2 -/



/- S is clopen proof Part 2(d) : {z ∈ U_y ∣ (proj_D ∘ H₁)(z) = (proj_D ∘ H₂)(z)} 
= {z ∈ U_y ∣ H₁(z) = H₂(z)} and {z ∈ U_y ∣ H₁(z) = H₂(z)} clopen by 2(c) and 
 -/



/- S is clopen proof Part 2(e) : S is clopen by Part 1 and Part 2(a) -/



/- Proof that S = Y using Lemma 3 -/





  sorry














