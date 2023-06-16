import Mathlib.Topology.Covering
import Mathlib.Topology.Connected 
import Mathlib.Topology.Basic
import Mathlib.Topology.IsLocallyHomeomorph
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.SetTheory.Cardinal.Basic 
import Mathlib.Topology.LocallyConstant.Basic
open Cardinal Topology

set_option autoImplicit false
set_option maxHeartbeats 0

namespace IsCoveringMap

variable {E X : Type _} [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (s t: Set X)



/- 

  Following lemma states that if a clopen set S ⊆ Y intersects with all the connected 
  components of Y, then S = Y

  main idea in the proof: If a clopen set intersects a connected component then 
  the clopen set must contain that connected component 
  
-/

#check IsClopen.connectedComponent_subset


lemma clopen_set_intersect_connected_components_whole_set (Y: Type _) [TopologicalSpace Y]
  (S : Set Y) (hS : IsClopen S) (w : ∀ x : Y, ∃ y ∈ connectedComponent x, y ∈ S) :
  S = Set.univ := by 
  apply Set.eq_univ_of_forall 
  intro x 
  specialize w x 
  cases' w with y h1
  have con_same : connectedComponent x = connectedComponent y := connectedComponent_eq (h1.1)
  have y_con: connectedComponent y ⊆ S := by 
    apply IsClopen.connectedComponent_subset   
    exact hS
    exact h1.2
  have con_sub : connectedComponent x ⊆ S := by 
    rw[con_same] 
    exact y_con
  have x_in_con : x ∈ connectedComponent x := mem_connectedComponent 
  exact con_sub x_in_con 


/- 
    Following key theorem states that a set A ⊆ Y is open in Y ↔ for every y ∈ Y 
    there is a nbhd U_y of y such that U_y ∩ A is open in U_y 

    Follows by parsing the definitions

    Note that this is an if and only if statement
-/


#check mem_nhds_iff
#check Set.inter_subset_left
#check IsOpen.preimage
#check continuous_inclusion
#check isOpen_iff_forall_mem_open



lemma is_open_of_is_open_coe (Y:Type _) [TopologicalSpace Y] (A: Set Y)
    (hA : ∀ x : Y, ∃ (U : Set Y) (_ : U ∈ 𝓝 x), 
    IsOpen ((Subtype.val : U → Y) ⁻¹' A)) : IsOpen A := by 

    rw[isOpen_iff_forall_mem_open] 
    intro x 
    specialize hA x 
    intro xA 
    rcases hA with ⟨ U, UNx, W, Wopen,hW⟩
    have hW1: W ∩ U = A ∩ U := by
      rw[← Subtype.preimage_val_eq_preimage_val_iff]
      exact hW
    have UNx':∃ V, V ⊆ U ∧ IsOpen V ∧ x ∈ V := by
      rw [← mem_nhds_iff]
      exact UNx
    rcases UNx' with ⟨V,VU,Vopen,xV⟩ 
    use W ∩ V
    constructor
    rintro v ⟨ vW,vV⟩
    apply Set.inter_subset_left A U  
    rw [← hW1]
    constructor
    exact vW
    apply VU
    exact vV
    constructor
    exact IsOpen.inter Wopen Vopen
    constructor
    apply Set.inter_subset_left W U
    rw [hW1]
    constructor
    exact xA
    apply VU
    exact xV
    exact xV


/- 
    Corollary of the above theorem is that a set A ⊆ Y is closed in Y ↔ for every y ∈ Y 
    there is a nbhd U_y of y such that U_y ∩ A is closed in U_y

    Follows by using above theorem for complement of A  
-/


lemma is_closed_of_is_closed_coe (Y:Type _) [TopologicalSpace Y] (A: Set Y)
(hA : ∀ x : Y, ∃ (U : Set Y) (_ : U ∈ 𝓝 x), IsClosed ((Subtype.val : U → Y) ⁻¹' A)) : IsClosed A := by 
  rw [← isOpen_compl_iff]
  apply is_open_of_is_open_coe 
  intro x 
  specialize hA x 
  cases' hA with hleft hright 
  cases' hright with h1 h2 
  use hleft 
  use h1 
  dsimp only [Set.preimage_compl] 
  rw [isOpen_compl_iff]
  exact h2   


/- 
    A direct consequence is that a set A ⊆ Y is clopen in Y ↔ for every y ∈ Y 
    there is a nbhd U_y of y such that U_y ∩ A is clopen in U_y

    Follows as a consequence of the previous two theorems  
-/


lemma is_clopen_of_is_clopen_coe (Y:Type _) [TopologicalSpace Y] (A: Set Y)
(hA : ∀ x : Y, ∃ (U : Set Y) (_ : U ∈ 𝓝 x), IsClopen ((Subtype.val : U → Y) ⁻¹' A)) : IsClopen A := by
  have left : IsOpen A := by
    apply is_open_of_is_open_coe Y A 
    intro x 
    specialize hA x 
    cases' hA with hleft hright
    use hleft 
    cases' hright with hleft hright
    use hleft 
    exact hright.1 

  have right : IsClosed A := by
    apply is_closed_of_is_closed_coe Y A 
    intro x 
    specialize hA x 
    cases' hA with hleft hright
    use hleft 
    cases' hright with hleft hright
    use hleft 
    exact hright.2 

  exact ⟨left, right ⟩ 


/- 
 
    Following lemma states that if f, g : X → Y are continuous and Y is a discrete topological
    space, then {x ∈ X ∣ f(x) = g(x)} is clopen in X 
    
    Main idea is to construct the function (f, g) : X → Y × Y.
    Then {x ∈ X ∣ f(x) = g(x)} is the inverse image of the diagonal in Y × Y.

-/


theorem clopen_equalizer_of_discrete (Y:Type _) [TopologicalSpace Y]
  [DiscreteTopology Y] {h g : X → Y} (hf : Continuous h) (hg : Continuous g) :
  IsClopen {x : X | h x = g x} := by 
  have diag_cl : IsClopen (Set.diagonal Y) := by 
    apply isClopen_discrete
  have con_map : Continuous (fun x => (g x, h x)) := by
    apply continuous_prod_mk.mpr 
    constructor 
    exact hg 
    exact hf 
  have : IsClopen (((fun x => (g x, h x))) ⁻¹' (Set.diagonal Y)) := by
    apply IsClopen.preimage
    exact diag_cl
    exact con_map
  have re : (fun x => (g x, h x)) ⁻¹' Set.diagonal Y = {x |h x = g x} := by 
    ext n  
    simp only [Set.mem_preimage, Set.mem_diagonal_iff, Set.mem_setOf_eq]
    tauto 
  rw[←re]
  exact this


--- Statement of the Theorem ---




/-
      

          Y -------------->  X               
         ^  \                ^ 
         |   \               |
         |       \ H₂        |
         |        \          |  f ;   if the triangles commute then H₁=H₂.  
         |      H₁     \     |
         |              \    |
         |                >  |
        Π₀Y  ------------->  E             

-/

theorem uniqueness_of_homotopy_lifting (Y : Type _) [TopologicalSpace Y] (hf : IsCoveringMap f)
  (H₁ H₂ : ContinuousMap Y E) (h : f ∘ H₁ = f ∘ H₂)
  (hC : ∀ x : Y, ∃ y ∈ connectedComponent x, H₁ y = H₂ y) :
  H₁ = H₂ := by 


/- Define S := {y ∈ Y ∣ H₁(y) = H₂(y)} -/

  let S:= {y:Y | H₁ y = H₂ y}

  have fCont: Continuous f:= IsCoveringMap.continuous hf 
  have H₁Cont: Continuous H₁:= ContinuousMap.continuous H₁ 
  have H₂Cont: Continuous H₂:= ContinuousMap.continuous H₂


  have ClopenS : IsClopen S := by

    /- 
    
    By Lemma is_clopen_of_is_clopen_coe it suffices 
    to prove that for every y there is open U_y that U_y ∩ S is clopen in U_y 

    -/

    apply is_clopen_of_is_clopen_coe
    intro y
    
    let x:=(f (H₁ y))
    specialize hf (x)
    rcases hf with ⟨DT, TrivN, xTrivN ⟩   
    let U_y := ((f∘ H₁)⁻¹' TrivN.baseSet)
    
    have hFu : ∀ u' ∈ U_y , (f ∘ H₂) u' ∈ TrivN.baseSet := by 
          intro u'
          intro Q
          show u' ∈ (f ∘ H₂)⁻¹' (TrivN.baseSet)  
          rw [← h]
          exact Q

    have UyNy: U_y∈ 𝓝 y:= by
      rw [IsOpen.mem_nhds_iff]
      · exact xTrivN
      apply  Continuous.isOpen_preimage 
      · exact Continuous.comp fCont H₁Cont
      · exact TrivN.open_baseSet

    have FuU_yEq :∀ u:U_y, f (H₁ u) = f (H₂ u) := by
        intro u
        calc
        f (H₁ u)=(f∘  H₁) u:=  rfl
        _=(f∘ H₂) u:= by rw [h]

    use  U_y  
    
    
    use UyNy
    dsimp only [Set.preimage_setOf_eq]
    
    have key : ∀ u : U_y, H₁ u = H₂ u ↔ (TrivN (H₁ u)).2 = (TrivN (H₂ u)).2 := by
      intro u
      
      have FuBaseSet : (f ∘ H₂) u ∈ TrivN.baseSet :=  (hFu u) (Subtype.mem u)
        
      
      constructor
      intro H₁ueqH₂u
      · exact congrArg Prod.snd (congrArg (↑TrivN) H₁ueqH₂u)
      
      
      
      have H₁uSource: H₁ u ∈ TrivN.source:= by
        rw [TrivN.mem_source]
        rw [FuU_yEq u]
        exact FuBaseSet

      have H₂uSource: H₂ u ∈ TrivN.source:= by
        rw [TrivN.mem_source]
        exact FuBaseSet

      intro H₁ProjeqH₂Proj
      apply TrivN.injOn 
      
      exact H₁uSource
      exact H₂uSource
      
      
      ext

      rw [TrivN.proj_toFun (H₁ u) H₁uSource]
      rw [TrivN.proj_toFun (H₂ u) H₂uSource]
      
      exact FuU_yEq u
      exact congrArg Subtype.val H₁ProjeqH₂Proj
    
    simp_rw [key]
    
    apply clopen_equalizer_of_discrete
    apply Continuous.snd 
    
    have H₁USource: ∀ u : U_y, H₁ ((Subtype.val : U_y → Y) u) ∈ TrivN.source:= by 
      simp only [Subtype.forall, Set.mem_preimage, Function.comp_apply]
      intro var
      rw[ TrivN.mem_source]
      simp only [imp_self]

    exact TrivN.continuous_toFun.comp_continuous (H₁Cont.comp continuous_subtype_val) H₁USource
    
    apply Continuous.snd
    
    have H₂USource: ∀ u : U_y, H₂ ((Subtype.val : U_y → Y) u) ∈ TrivN.source:= by 
      simp only [Subtype.forall, Set.mem_preimage, Function.comp_apply]
      intro var
      rw[ TrivN.mem_source]
      have FuEq : f (H₁ var) = f (H₂ var) := by
        calc
        f (H₁ var)=(f∘  H₁) var:=  rfl
        _=(f∘ H₂) var:= by rw [h]
      rw [FuEq]
      simp only [imp_self]
    exact TrivN.continuous_toFun.comp_continuous (H₂Cont.comp continuous_subtype_val) H₂USource




  have SEqUniv : S = Set.univ := by 
    apply clopen_set_intersect_connected_components_whole_set 
    exact ClopenS 
    exact hC 
  
  ext z
  
  have zS : z ∈ S := by  
    rw [SEqUniv]
    exact trivial 
  
  exact zS 
   



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



/- Define S := {y ∈ Y ∣ H₁(y) = H₂(y)} -/
  

/- S is clopen proof Part 1 : by Lemma 1 it suffices to prove that U_y ∩ S is
clopen in U_y (where for y ∈ Y, F(y) ∈ X has evenly covered nbhd V_y by defn
of covering and U_y := F^{-1}(V_y)) -/
