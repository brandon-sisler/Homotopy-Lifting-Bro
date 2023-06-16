import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.PathConnected
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
open Set Topology

variable {X : Type _} [TopologicalSpace X] (x₀ : X) {x₁ : X }

--#synth TopologicalSpace (Path x₀ x₁)

open TopologicalSpace
open ContinuousMap

def inc_path {X: Type _} [TopologicalSpace X] 
         (U: Set X) (x y: U) (p : Path x y): Path (x:X) (y:X) where
      toFun t := p t
      continuous_toFun := by continuity  
      source' := by simp
      target' := by simp
#check Subtype

def inc_path_subset {X: Type _} [TopologicalSpace X] 
         {U V: Set X}(x y:X) (h: x ∈ V) (g: y ∈ V) (VU: V ⊆ U) 
          (p : Path (X := V) ⟨ x, h ⟩ ⟨ y , g ⟩ ): Path (X := U) ⟨ x, (VU h) ⟩ ⟨ y, (VU g) ⟩ where
      toFun t := ⟨ (p t).1, VU (p t).2 ⟩ 
      continuous_toFun := by continuity  
      source' := by simp
      target' := by simp

def slsc_subspace {X: Type _} [TopologicalSpace X](x:X)(U: Set X) : Prop :=
  ∃ (hx : x ∈ U), ∀ p : Path (X := U) ⟨x, hx⟩ ⟨x, hx⟩, Path.Homotopic (inc_path _ _ _ p) (Path.refl _) 

--Subset of a semi-locally-simply-connected subset is semi locally simply connected
lemma subset_slsc_is_slsc {X: Type _} [TopologicalSpace X] (x:X){U V: Set X} (slscU: slsc_subspace x U) (VU: V ⊆ U)(xinV: x ∈ V):
  slsc_subspace x V := by 
    use xinV
    intro loopV 
    rcases slscU with ⟨ xinU, loopU_hom_const ⟩ 
    let loopV_to_U := inc_path_subset x x xinV xinV VU loopV
    let loopV_to_X := inc_path _ _ _  loopV
    let loopV_to_U_to_X := inc_path _ _ _  loopV_to_U
    have this1: loopV_to_X = loopV_to_U_to_X := by 
      ext t 
      simp [inc_path, inc_path_subset]
    specialize loopU_hom_const loopV_to_U
    have same_is_hom: Path.Homotopic loopV_to_X loopV_to_U_to_X := by
      rw [this1]
    have loopV_to_X_hom_const :  Path.Homotopic loopV_to_X (Path.refl _) := by
      exact Path.Homotopic.trans same_is_hom loopU_hom_const
    exact loopV_to_X_hom_const 

def slsc_pc_subspace {X: Type _} [TopologicalSpace X] (U: Set X) : Prop :=
  ∃ x, slsc_subspace x U ∧ IsPathConnected U ∧ U.Nonempty

class slsc_space (X: Type _)[TopologicalSpace X] where
   slsc_nbhd_exists : ∀ x : X, ∃ U : Set X, IsOpen U ∧  slsc_subspace x U 

-- Define the potential basis whose elements are slsc and path connected
def slsc_pc_nbhds (X: Type _)[TopologicalSpace X]: Set (Set X):= 
  { U : Set X | IsOpen U ∧ slsc_pc_subspace U } 


open Topology Filter

-- A locally path connected space is a locally connected space
instance [TopologicalSpace X] [LocPathConnectedSpace X] : LocallyConnectedSpace X := by
    apply locallyConnectedSpace_of_connected_bases
    exact path_connected_basis
    rintro x U ⟨-, hU⟩
    exact hU.isConnected.2

--Patrick's lemma that a locally path connected space has a path connected and open basis for the neighborhood filter
lemma path_connected_open_basis [TopologicalSpace X] [LocPathConnectedSpace X] (x : X) :
    (𝓝 x).HasBasis (fun s ↦ s ∈ 𝓝 x ∧ IsOpen s ∧ IsPathConnected s) id := by
  constructor
  intro U
  rw [(path_connected_basis x).mem_iff]
  constructor
  · rintro ⟨V, ⟨V_in, -⟩, VU : V ⊆ U⟩
    rcases (nhds_basis_opens x).mem_iff.mp V_in with ⟨W, ⟨xW, W_op⟩, WV⟩
    refine ⟨connectedComponentIn W x, ⟨?_, ?_, ?_⟩, ?_⟩
    · exact W_op.connectedComponentIn.mem_nhds (mem_connectedComponentIn xW)
    · exact W_op.connectedComponentIn
    · rw [W_op.connectedComponentIn.isConnected_iff_isPathConnected]
      exact isConnected_connectedComponentIn_iff.mpr xW
    · exact (connectedComponentIn_subset W x).trans (WV.trans VU)
  · rintro ⟨V, ⟨V_in, -, hV⟩, hVU : V ⊆ U⟩
    exact ⟨V, ⟨V_in, hV⟩, hVU⟩

lemma inter_sub_left {X : Type _}(U W : Set X) : U ∩ W ⊆ U := by
  simp

lemma inter_sub_right {X : Type _}(U W : Set X) : U ∩ W ⊆ W := by
  simp

-- To show that the slsc and path connected collection is a basis when X is a locally path connected space
lemma slsc_pc_nbhds_is_basis {X: Type _}[TopologicalSpace X][lpc: LocPathConnectedSpace X][slsc: slsc_space X]:
  IsTopologicalBasis (slsc_pc_nbhds X) :=by 
  apply isTopologicalBasis_of_open_of_nhds

  . intro U Uslpc
    exact Uslpc.1

  . intro a U ainU openU
    rcases slsc_space.slsc_nbhd_exists a with ⟨ W , ⟨openW, ⟨ ainW , slsc_conditionW ⟩ ⟩ ⟩ 
    have slscW : slsc_subspace a W := by 
      use ainW
      exact slsc_conditionW
    have openUW : IsOpen (U ∩ W):= TopologicalSpace.isOpen_inter U W openU openW
    have ainUW : a ∈ U ∩ W := ⟨ ainU , ainW ⟩ 
    have UW_in : (U ∩ W) ∈ 𝓝 a := openUW.mem_nhds ainUW
    have slscUW : slsc_subspace a (U ∩ W):= by exact subset_slsc_is_slsc a slscW (inter_sub_right U W) ainUW
    rcases (path_connected_open_basis a).mem_iff.mp UW_in with ⟨ V, ⟨ V_in, openV , pcV⟩ , hVUW : V ⊆ U ∩ W⟩  
    rcases mem_nhds_iff.mp V_in with ⟨S, ⟨ hSV, openS, ainS ⟩ ⟩
    have slscV : slsc_subspace a V:= by exact subset_slsc_is_slsc a slscUW hVUW (hSV ainS)
    use V
    constructor 
    . exact ⟨ openV, ⟨ a, ⟨ slscV , pcV, ⟨ a, hSV ainS⟩ ⟩ ⟩⟩  
    . constructor
      . exact hSV ainS
      . exact subset_trans hVUW (inter_sub_left U W) 


/- 
Our neighborhood basis is assumed to consist of non-empty sets, the purpose of get_point 
is to use choice to select a point from each these sets and the follow up lemma is used 
to show we can always do this.
-/

noncomputable
def get_point {X: Type _} (U : Set  X) (h : U.Nonempty) : X := h.choose

lemma slsc_nbhd_is_nonempty (X : Type _) [TopologicalSpace X] {U : Set X} (h : U ∈ slsc_pc_nbhds X ) : U.Nonempty := by
  simp only [slsc_pc_nbhds] at h
  obtain ⟨_, h₁⟩ := h 
  simp only [slsc_pc_subspace] at h₁
  obtain ⟨_ , _, _ , h₂ ⟩ := h₁   
  exact h₂  

/-
  Here we define the underlying "set" for a space we intend to topologize and prove it possesses a covering projection.

  The universal cover is defined to be the quotient of the path space of X modulo the equivalence 
  relation generated by homotopy classes of paths. So long as X satisfies the conditions of being 
  locally path connected and semilocally simply connected, one may show that 
  this construction admits a covering projection onto X and that it is simply connected. 
-/

def UniversalCover (X: Type _) [TopologicalSpace X] (x₀ : X) :=
  Σ x₁ : X , Path.Homotopic.Quotient x₀ x₁

/-
Let U be a one of our simply connected open subsets of X.

Select a representative point xᵤ ∈ U and let u ∈ U be some other point. 
A point in the universla cover corresponds to a homotopy class [γᵤ] of paths connecting x₀ to u. 
Since we are assuming each U is path-connected, the homotopy class of γ depends only on the homotopy 
class of the path used to connect x₀ to xᵤ.
-/
def get_point_in_UniversalCover (X: Type _)[TopologicalSpace X] ( x₀ : X ) (U : Set X) (h : U ∈ slsc_pc_nbhds X) 
  ( γ : Path x₀ (get_point U (slsc_nbhd_is_nonempty X h))) (u : U) : UniversalCover X x₀ :=
  Quotient.comp ⟦γ⟧ ⟦Path (get_point U (slsc_nbhd_is_nonempty X h)) u ⟧
  sorry

def all_local_compositions (X: Type _)[TopologicalSpace X] ( x₀ : X ) (U : Set X) (h : U ∈ slsc_pc_nbhds X) 
  ( γ : Path x₀ (get_point U (slsc_nbhd_is_nonempty X h ))): Set ( UniversalCover X x₀ ) := 
  get_point_in_UniversalCover X x₀ U h γ '' Set.univ 

/-
lifts_of_slsc_pc_nbhds creates a collection of subsets of the universal cover as follows.

For each element U in the basis of simply connected sets, select a representative point xᵤ
and for each homotopy class [γ] of paths connecting x₀ to xᵤ, we create the set 

    U_γ  := {[γᵤ] | η : I → U such that [γᵤ] = [η ∘ γ] }.

Since each U is path connected and simply connected by assumption, the homotopy class of η is 
determined by its endpoints and standard results on homotopy classes of concatenations of path
tell us the homotopy class of γᵤ is determined by the homotopy class of γ. 

The construction allows one to construct a bijection between points in U_γ and points in U and
a bit more work allows us to say this bijection is a homeomorphism. 

-/        
def lifts_of_slsc_pc_nbhds (X : Type _) [TopologicalSpace X ] (x₀ : X) 
 : Set (Set (UniversalCover X x₀)) :=

  range fun p : ( Σ U : slsc_pc_nbhds X , Path x₀ (get_point U.1 (slsc_nbhd_is_nonempty X U.2 )) ) 
    ↦  all_local_compositions X x₀ p.1.1 p.1.2 p.2  --all_local_compositions X x₀ p.1 _ --p.2

/-
Now we give UniversalCover the topology one generated by lifts_of_slsc_pc_nbhds
-/
instance (X : Type _) [TopologicalSpace X] [LocPathConnectedSpace X] [slsc_space X] (x₀ : X) : TopologicalSpace (UniversalCover X x₀) :=  
  generateFrom (lifts_of_slsc_pc_nbhds X x₀)

--Need to prove the U_γ are actually U_[γ] aka independence of homotopy class of γ

--Lemma to prove propert (*) in hatcher
lemma property_star {X: Type _} [TopologicalSpace X] [lpc: LocPathConnectedSpace X] 
  [slsc: slsc_space X] {x₀ : X} (Y : UniversalCover X x₀) (y: Y) (U : Set X) (h : U ∈ slsc_pc_nbhds X) 
  ( γ : Path x₀ (get_point U (slsc_nbhd_is_nonempty X h ))) (U_gamma : all_local_compositions X x₀ U h γ)
  : y ∈ U_gamma → all_local_compositions X x₀ U h y:= by sorry

lemma lifts_of_slsc_pc_nbhds_is_basis {X: Type _} [TopologicalSpace X] [lpc: LocPathConnectedSpace X] 
  [slsc: slsc_space X] (x₀ : X) (Y : UniversalCover X x₀) :
  IsTopologicalBasis (lifts_of_slsc_pc_nbhds X x₀) := by sorry 
  -- Here we will prove that the lifts of the basis sets form a basis for the topology they generate on the UniversalCover 

