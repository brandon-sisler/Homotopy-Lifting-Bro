--import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Homotopy.basic
import Mathlib.Topology.IsLocallyHomeomorph
--import Mathlib.Topology.FiberBundle.basic
import Mathlib.Topology.LocallyConstant.basic
import Mathlib.SetTheory.cardinal.basic
import Mathlib.Topology.Covering


open Set Filter Topology


variable (f)

























/- Lemma 1 stating that a set S ⊆ Y is clopen in Y ↔ ∀ y ∈ Y ∃ nbhd U_y of y 
such that U_y ∩ S is clopen in U_y -/



/- Lemma 1 proof -/



/- Lemma 2 stating that if f, g : X → Y are continuous and Y is a discrete topological
space, then {x ∈ X ∣ f(x) = g(x)} is clopen in X -/



/- Lemma 2 proof -/


--- Statement of the Theorem ---


theorem Uniqueness_Of_Homotopy_Lifting (Y X E: Type _) 
[TopologicalSpace Y][TopologicalSpace X][TopologicalSpace E]
(f:ContinuousMap E X)(hf: IsCoveringMap f)
(H₁ H₂ : ContinuousMap Y E)(h: f ∘ H₁ = f ∘ H₂)
(hC : ∀ x : Y, ∃ y ∈ connectedComponent x, H₁ y = H₂ y) : H₁ = H₂  := by sorry


/- Define S := {y ∈ Y ∣ H₁(y) = H₂(y)} -/



/- S is clopen proof Part 1 : by Lemma 1 it suffices to prove that U_y ∩ S is
clopen in U_y (where for y ∈ Y, F(y) ∈ X has evenly covered nbhd V_y by defn
of covering and U_y := F^{-1}(V_y)) -/



/- S is clopen proof Part 2(a) : U_y ∩ S = {z ∈ U_y ∣ H₁(z) = H₂(z)} -/



/- S is clopen proof Part 2(b) : ∃ discrete topological space D such that 
f⁻¹(V_y) ≅ V_y × D := by defn of covering -/



/- S is clopen proof Part 2(c) : {z ∈ U_y ∣ (proj_D ∘ H₁)(z) = (proj_D ∘ H₂)(z)} is clopen in U_y := 
by Lemma 2 -/



/- S is clopen proof Part 2(d) : {z ∈ U_y ∣ (proj_D ∘ H₁)(z) = (proj_D ∘ H₂)(z)} 
= {z ∈ U_y ∣ H₁(z) = H₂(z)} and {z ∈ U_y ∣ H₁(z) = H₂(z)} clopen by 2(c) and 
 -/



/- S is clopen proof Part 2(e) : S is clopen by Part 1 and Part 2(a) -/



/- Proof that S clopen in Y connected → S = Y or S = ∅ -/



/- (S ≠ ∅ := by Statement hypothesis) → S = Y → H₁(y) = H₂(y) ∀ y ∈ Y -/

















