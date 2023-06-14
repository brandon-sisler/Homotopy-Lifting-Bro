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





--Definition of local path connectedness
--(From Topology.PathConnected)

-- class lpc_space {X: Type _} [TopologicalSpace X] where
--   lpc_cond: ∀ x : X, ∀ U ∈ (nhds x).sets ∧ IsPathConnected U, ∃ V : 𝓝 x, IsPathConnected v


-- ∀ \gamma : Path x x , 

--When is a  U :Set X with x ∈ U ⊂ X a semi local simply connected neighborhood?
-- ⟨ x, h ⟩ 

def slsc_subspace {X: Type _} [TopologicalSpace X](x:X)(U: Set X) : Prop := x ∈ U ∧ x ∈ U 

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
    
    have OpenUW : IsOpen (U ∩ W):= TopologicalSpace.isOpen_inter U W openU openW
    have slscUW : slsc_subspace a (U ∩ W):= by sorry
    have ainUW : a ∈ U ∩ W := ⟨ ainU , ainW ⟩ 
    
    --have U_in : U ∈ 𝓝 a := openU.mem_nhds ainU 
    --rcases(path_connected_basis a).mem_iff.mp U_in with ⟨V, ⟨V_in, hV⟩, hVU : V ⊆ U⟩
    
    
  

-- Define a potential basis for CoverSet using the slsc_pc_nbhds basis of X\


def coverSet :=
  Σ x₁ : X , Path.Homotopic.Quotient x₀ x₁




#exit


Sigma 