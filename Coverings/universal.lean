import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.PathConnected
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
open Set Topology

variable {X : Type _} [TopologicalSpace X] (x₀ : X) {x₁ : X }

-- #synth TopologicalSpace (Path x₀ x₁)

open TopologicalSpace
open ContinuousMap
 
def inc_path {X: Type _} [TopologicalSpace X] 
         (U: Set X) (x y: U) (p : Path x y): Path (x:X) (y:X) where
      toFun t := p t
      continuous_toFun := by continuity --p.continuous_toFun  
      source' := by simp
      target' := by simp

def slsc_subspace {X: Type _} [TopologicalSpace X](x:X)(U: Set X) : Prop :=
  ∃ (hx : x ∈ U), ∀ p : Path (X := U) ⟨x, hx⟩ ⟨x, hx⟩, Path.Homotopic (inc_path _ _ _ p) (Path.refl _) 

lemma subset_slsc_is_slsc {X: Type _} [TopologicalSpace X] (x:X){U V: Set X} (slscU: slsc_subspace x U) (VU: V ⊆ U)(xinV: x ∈ V):
  slsc_subspace x V := by sorry 

def slsc_pc_subspace {X: Type _} [TopologicalSpace X] (U: Set X) : Prop :=
  ∃ x, slsc_subspace x U ∧ IsPathConnected U ∧ U.Nonempty

class slsc_space (X: Type _)[TopologicalSpace X] where
   slsc_nbhd_exists : ∀ x : X, ∃ U : Set X, IsOpen U ∧  slsc_subspace x U 

-- Define the potential basis whose elements are slsc and path connected
def slsc_pc_nbhds (X: Type _)[TopologicalSpace X]: Set (Set X):= 
  { U : Set X | IsOpen U ∧ slsc_pc_subspace U } 

-- To show that the slsc and path connected collection is a basis when X is a locally path connected space
lemma slsc_pc_nbhds_is_basis {X: Type _}[TopologicalSpace X][lpc: LocPathConnectedSpace X][slsc: slsc_space X]:
  IsTopologicalBasis (slsc_pc_nbhds X) :=by 
  apply isTopologicalBasis_of_open_of_nhds

  . intro U Uslpc
    exact Uslpc.1

  . intro a U ainU openU
    rcases slsc_space.slsc_nbhd_exists a with ⟨ W , ⟨openW, ⟨ ainW , slsc_condition ⟩ ⟩ ⟩ 
    
    have openUW : IsOpen (U ∩ W):= TopologicalSpace.isOpen_inter U W openU openW
    -- have slscUW : slsc_subspace a (U ∩ W):= by sorry
    have ainUW : a ∈ U ∩ W := ⟨ ainU , ainW ⟩ 
    have UW_in : (U ∩ W) ∈ 𝓝 a := openUW.mem_nhds ainUW
    have this:= (path_connected_basis a).mem_iff.mp UW_in 
    rcases this with ⟨V, ⟨V_in, hV⟩, hVU : V ⊆ U ∩ W⟩
    have new:= mem_nhds_iff.mp V_in 
    rcases new with ⟨S, ⟨ hSV, openS, ainS ⟩ ⟩
    have slscS : slsc_subspace a S:= by sorry
    use S
    constructor 
    . constructor
      exact openS
      use a
      


    . constructor
      exact ainS
      intro x xs
      exact (hVU (hSV xs)).1
      
      -- have : S ⊆ U := by  
      -- exact ⟨ ainS, ⟩ 
    --have U_in : U ∈ 𝓝 a := openU.mem_nhds ainU 
    --rcases(path_connected_basis a).mem_iff.mp U_in with ⟨V, ⟨V_in, hV⟩, hVU : V ⊆ U⟩

noncomputable
def get_point {X: Type _} (U : Set  X) (h : U.Nonempty) : X := h.choose

lemma slsc_nbhd_is_nonempty (X : Type _) [TopologicalSpace X] (U : slsc_pc_nbhds X) : U.1.Nonempty :=
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

