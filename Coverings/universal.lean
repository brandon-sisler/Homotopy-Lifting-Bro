import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.PathConnected
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
open Set Topology

variable {X : Type _} [TopologicalSpace X] (x₀ : X) {x₁ : X }
-- def baseSet : TopologicalSpace X 

#check X


--#check coverSet
#synth TopologicalSpace (Path x₀ x₁)

--example : IsOpen (univ : Cover) := 
 -- isOpen_univ

open TopologicalSpace


--Patrick's lemma that isn't applicable
example (X : Type _) (s : Set (Set X)) (h : ∀ U V : Set X, U ∈ s → V ⊆ U → V ∈ s)
  (h' : ∀ x: X, ∃ U ∈ s, x ∈ U) :
    IsTopologicalBasis (t := generateFrom s) s := by
  let _ := generateFrom s
  apply isTopologicalBasis_of_open_of_nhds
  · intros u hu
    exact isOpen_generateFrom_of_mem hu
  · intros x U hx hU
    induction hU with
    | basic V hV => use V, hV, hx
    | univ => simpa using h' x
    | inter V W _ _ h₃ h₄ =>
        rcases h₃ hx.1 with ⟨R, _, hxR, hRV⟩
        rcases h₄ hx.2 with ⟨S, S_in, hxS, hSW⟩
        refine ⟨R ∩ S, ?_, ⟨hxR, hxS⟩, ?_⟩
        · exact h _ _ S_in (Set.inter_subset_right R S)
        · exact Set.inter_subset_inter hRV hSW
    | sUnion S _ hS =>
        rcases hx with ⟨T, T_in, hxT⟩
        rcases hS T T_in hxT with ⟨V, V_in, hxV, hVT⟩
        use V, V_in, hxV
        exact Set.subset_sUnion_of_subset S T hVT T_in







-- class lpc_space {X: Type _} [TopologicalSpace X] where
--   lpc_cond: ∀ x : X, ∀ U ∈ (nhds x).sets ∧ IsPathConnected U, ∃ V : 𝓝 x, IsPathConnected v


-- ∀ \gamma : Path x x , 
open ContinuousMap

--Locally Path connected without filters

-- def lpc_subset_of_nbhd {X: Type _}[TopologicalSpace X][lpc: LocPathConnectedSpace X]
--       (x:X){U: Set X}(xinU: x ∈ U)(openU: IsOpen U): Set X ∧ := by
--         have U_in : U ∈ 𝓝 x := openU.mem_nhds xinU
--         have this := (path_connected_basis x).mem_iff.mp U_in
--         have V:= this.choose
--         sorry
--         --rcases this with ⟨V, ⟨V_in, hV⟩, hVU⟩



-- Semi Simply connected: 
def inc_path {X: Type _} [TopologicalSpace X] 
         (U: Set X) (x y: U) (p : Path x y): Path (x:X) (y:X) where
      toFun t := p t
      continuous_toFun := by continuity --p.continuous_toFun  
      source' := by simp
      target' := by simp


--When is a  U :Set X with x ∈ U ⊂ X a semi local simply connected neighborhood?
-- ⟨ x, h ⟩ 

def slsc_subspace {X: Type _} [TopologicalSpace X](x:X)(U: Set X) : Prop :=
  ∃ (hx : x ∈ U), ∀ p : Path (X := U) ⟨x, hx⟩ ⟨x, hx⟩, Path.Homotopic (inc_path _ _ _ p) (Path.refl _) 


lemma subset_slsc_is_slsc {X: Type _} [TopologicalSpace X] (x:X){U V: Set X} (slscU: slsc_subspace x U) (VU: V ⊆ U)(xinV: x ∈ V):
  slsc_subspace x V := by sorry 

-- TODO:
-- 1. Tell Lean U is a subspace of X
-- 2. indicate i^{-1}(x) : U
-- 3. Use i which we should get from 1 to create a object 
-- i ∘ γ : Path x x where \gamma : Path i^{-1}(x) i^{-1} (x)
-- 4. Prove [i ∘ γ ] = [x] where latter is the constant path at x.


def slsc_pc_subspace {X: Type _} [TopologicalSpace X] (U: Set X) : Prop :=
  ∃ x, slsc_subspace x U ∧ IsPathConnected U

class slsc_space (X: Type _)[TopologicalSpace X] where
   slsc_nbhd_exists : ∀ x : X, ∃ U : Set X, IsOpen U ∧  slsc_subspace x U 

#check slsc_space.slsc_nbhd_exists

-- To show the path connected subsets of X is a basis
--(Possibly use the basis from Topology.PathConnected)


-- Define the potential basis whose elements are slsc and path connected
--(Make this smaller)
def slsc_pc_nbhds (X: Type _)[TopologicalSpace X]: Set (Set X):= 
  { U : Set X | IsOpen U ∧ slsc_pc_subspace U} 

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

-- We will use this to get a map that assigns to each non-empty subset of X a point in it

-- curly braces {} it so that one does not need to specify a space
def get_point {X: Type _} (U : Set  X) : X := 
 sorry



-- The universal cover is defined to be the quotient of     
def UniversalCover (X: Type _) [TopologicalSpace X] (x₀ : X) :=
  Σ x₁ : X , Path.Homotopic.Quotient x₀ x₁

variable (g : Path.Homotopic.Quotient x₀ x₁)



def temp (X: Type _)[TopologicalSpace X] ( x₀ : X ) (U : Set X) ( γ : Path x₀ (get_point U)) (u : U) : UniversalCover X x₀ :=
  have test : Path.Homotopic.Quotient x₀ ( get_point U ) := by sorry
  -- try to get the specific γ₁ on its own so that we can use get_all_local_compositions together as a set
  -- Σ u : U, { γ₁ : UniversalCover X x₀ | ∃ γ₀ : Path ( get_point U )  u , γ₁ =  ⟨ _ , ⟦ γ.trans ( inc_path U ( get_point U ) u γ₀ ) ⟧ ⟩ }
  thingy := ⟨ x₀ , test ⟩

def all_local_compositions (X: Type _)[TopologicalSpace X] ( x₀ : X ) (U : slsc_pc_nbhds X) ( γ : Path x₀ (get_point U)): Set ( UniversalCover X x₀ ) := 
  temp X x₀ U γ '' Set.univ 

  

-- lifts_of_slsc_pc_nbhds creates a collection of subsets of the universal cover which correspond
-- to each homotopy equivalence class of paths
def lifts_of_slsc_pc_nbhds (X : Type _) [TopologicalSpace X ] (x₀ : X) ( U : slsc_pc_nbhds X) ( γ : Path x₀ ( get_point U ) ) : Set ( Set ( UniversalCover X x₀ )) :=
  all_local_compositions X x₀ ''



lemma lifts_of_slsc_pc_nbhds_is_basis {X: Type _} [TopologicalSpace X] [lpc: LocPathConnectedSpace X] [slsc: slsc_space X] (x₀ : X) (Y : UniversalCover X x₀) :
  IsTopologicalBasis ( lifts_of_slsc_pc_nbhds X x₀ ) := by 
  apply isTopologicalBasis_of_open_of_nhds
--     sorry
--   sorry  

instance (X : Type _)[TopologicalSpace X] [LocPathConnectedSpace X] [slsc_space X] (x₀: X) : 
  TopologicalSpace (UniversalCover X x₀) where
  generateFrom(lifts_of_slsc_pc_nbhds X)
  sorry

