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
    . constructor
      exact openV
      use a
      constructor
      . exact slscV
      . constructor
        . exact pcV
        . sorry

    . constructor
      . exact hSV ainS
      . exact subset_trans hVUW (inter_sub_left U W) 

noncomputable
def get_point {X: Type _} (U : Set  X) (h : U.Nonempty) : X := h.choose

lemma slsc_nbhd_is_nonempty (X : Type _) [TopologicalSpace X] (U : slsc_pc_nbhds X) : U.1.Nonempty := by
  have h_expand : ∃ x : X , slsc_subspace x U.1 ∧ IsPathConnected U.1 ∧ U.1.Nonempty by := sorry
  
  


  sorry

  

-- The universal cover is defined to be the quotient of the path space of X modulo the equivalence relation generated     
def UniversalCover (X: Type _) [TopologicalSpace X] (x₀ : X) :=
  Σ x₁ : X , Path.Homotopic.Quotient x₀ x₁

def temp (X: Type _)[TopologicalSpace X] ( x₀ : X ) (U : slsc_pc_nbhds X) ( γ : Path x₀ (get_point U (slsc_nbhd_is_nonempty X U ) )) (u : U.1) : UniversalCover X x₀ :=
  

  -- try to get the specific γ₁ on its own so that we can use get_all_local_compositions together as a set
  -- Σ u : U, { γ₁ : UniversalCover X x₀ | ∃ γ₀ : Path ( get_point U )  u , γ₁ =  ⟨ _ , ⟦ γ.trans ( inc_path U ( get_point U ) u γ₀ ) ⟧ ⟩ }
  --thingy := ⟨ x₀ , test ⟩
  sorry

def all_local_compositions (X: Type _)[TopologicalSpace X] ( x₀ : X ) (U : slsc_pc_nbhds X) ( γ : Path x₀ (get_point U (slsc_nbhd_is_nonempty X U ))): Set ( UniversalCover X x₀ ) := 
  temp X x₀ U γ '' Set.univ 

#check fun p : Σ (U : slsc_pc_nbhds X), Path x₀ (get_point U (slsc_nbhd_is_nonempty X U ) ) ↦  all_local_compositions X x₀ p.1 p.2 

-- lifts_of_slsc_pc_nbhds creates a collection of subsets of the universal cover which correspond
-- to each homotopy equivalence class of paths
def lifts_of_slsc_pc_nbhds (X : Type _) [TopologicalSpace X ] (x₀ : X) 
 -- ( U : slsc_pc_nbhds X) ( γ : Path x₀ ( get_point U ) ) 
 : Set (Set (UniversalCover X x₀)) :=
  range (fun p : Σ (U : slsc_pc_nbhds X), Path x₀ (get_point U (slsc_nbhd_is_nonempty X U ) ) ↦  all_local_compositions X x₀ p.1 p.2)

instance (X : Type _) [TopologicalSpace X] [LocPathConnectedSpace X] [slsc_space X] (x₀ : X) : TopologicalSpace (UniversalCover X x₀) :=  
  generateFrom (lifts_of_slsc_pc_nbhds X x₀)

lemma lifts_of_slsc_pc_nbhds_is_basis {X: Type _} [TopologicalSpace X] [lpc: LocPathConnectedSpace X] [slsc: slsc_space X] (x₀ : X) (Y : UniversalCover X x₀) :
  IsTopologicalBasis (lifts_of_slsc_pc_nbhds X x₀) := by sorry 
  -- apply isTopologicalBasis_of_open_of_nhds
--     sorry
--   sorry  

