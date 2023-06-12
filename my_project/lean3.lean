import Mathlib.Topology.Covering
import Mathlib.Topology.IsLocallyHomeomorph
import Mathlib.Topology.FiberBundle.Basic

variable {α : Type}{E X : Type α} [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (s : Set X)

/-- A point `x : X` is evenly covered by `f : E → X` if `x` has an evenly covered neighborhood. -/

--`def IsEvenlyCovered (x : X) (I : Type _) [TopologicalSpace I] `:=
--  `DiscreteTopology I ∧ ∃ t : Trivialization I f, x ∈ t.baseSet`

theorem mk (F : X → Type α) [∀ x, TopologicalSpace (F x)] [hF : ∀ x, DiscreteTopology (F x)]
    (e : ∀ x ∈ s, Trivialization (F x) f) (h : ∀ (x : X) (hx : x ∈ s), x ∈ (e x hx).baseSet) :
    IsCoveringMapOn f s := fun x hx =>
  IsEvenlyCovered.to_isEvenlyCovered_preimage ⟨hF x, e x hx, h x hx⟩

--If f is a covering map, from covering space E to topological space X, then f is continuous
lemma continuous (hf : IsCoveringMap f) : Continuous f := by sorry

--If f is a covering map, then f is a local homeomorphism 
lemma is_locally_homeomorph (hf : IsCoveringMap f) : IsLocallyHomeomorph f := by sorry

--If f is a covering map, then it is an open map
lemma is_open_map (hf : IsCoveringMap f) : IsOpenMap f := by sorry

--If f is a covering map and a surjective function then it is a quotient map
lemma quotient_map (hf : IsCoveringMap f) (hf' : Function.Surjective f) : QuotientMap f := by sorry

-- `noncomputable def to_homeomorph (hf : IsCoveringMap f)`
--   `(h : Function.Bijective f) : Homeomorph E X :=`
--` Homeomorph.homeomorphOfContinuousOpen (equiv.of_bijective) hf.continuous hf.is_open_map`

-- `lemma is_locally_constant_card (hf : is_covering_map f) :`
--  ` is_locally_constant (λ x, #(f ⁻¹' {x})) := `
-- `(is_locally_constant.iff_exists_open _).2 $ λ x, let ⟨t, ht⟩ := (hf x).2 in`
--  ` ⟨_, t.open_base_set, ht, λ y hy, (t.preimage_singleton_homeomorph hy).to_equiv.cardinal_eq⟩`

lemma is_fiber_bundle.is_covering_map {F : Type α} [TopologicalSpace F] : IsCoveringMap f := by sorry

lemma clopen_set_intersect_connected_components_whole_set (Y: Type α) [TopologicalSpace Y]
  (S : Set Y) (hS : IsClopen S) (w : ∀ x : Y, ∃ y ∈ connectedComponent x, y ∈ S) :
  S = Set.univ := by sorry

lemma is_open_inter_of_coe_preim {X : Type α} [TopologicalSpace X] (s t : Set X) (hs : IsOpen s)
  --(h : IsOpen((coe : s → X) ⁻¹' t)) : IsOpen (t ∩ s) := by sorry

lemma is_open_of_is_open_coe (Y:Type α) [TopologicalSpace Y] (A: Set Y)
--(hA : ∀ x : Y, ∃ (U : Set Y) (hU : U ∈ 𝓝 x), IsOpen ((coe : U → Y) ⁻¹' A)) : IsOpen A := by sorry

lemma is_closed_of_is_closed_coe (Y:Type α) [TopologicalSpace Y] (A: Set Y)
--(hA : ∀ x : Y, ∃ (U : Set Y) (hU : U ∈ 𝓝 x), IsClosed ((coe : U → Y) ⁻¹' A)) : IsClosed A := by sorry

lemma is_clopen_of_is_clopen_coe (Y:Type α) [TopologicalSpace Y] (A: Set Y)
--(hA : ∀ x : Y, ∃ (U : Set Y) (hU : U ∈ 𝓝 x), is_clopen ((coe : U → Y) ⁻¹' A)) : IsClopen A : =by sorry 

theorem clopen_equalizer_of_discrete {X Y : Type α} [TopologicalSpace X] [TopologicalSpace Y]
  [DiscreteTopology Y] {f g : X → Y} (hf : Continuous f) (hg : Continuous g) :
  --IsClopen {x : X | f x = g x} := (is_clopen_discrete (set.diagonal Y)).preimage (hf.prod_mk hg)


lemma tautology : true := rfl

theorem uniqueness_of_homotopy_lifting (Y : Type α) [TopologicalSpace Y] (hf : IsCoveringMap f)
  (H₁ H₂ : ContinuousMap Y E) (h : f ∘ H₁ = f ∘ H₂)
  (hC : ∀ x : Y, ∃ y ∈ connectedComponent x, H₁ y = H₂ y) :
  H₁ = H₂ := by sorry

-- begin
--   refine fun_like.ext H₁ H₂ (set.eq_univ_iff_forall.mp
--     (clopen_set_intersect_connected_components_whole_set _ _
--     (is_clopen_of_is_clopen_coe _ _ (λ x, _)) hC)),
--   let t := (hf (f (H₁ x))).to_trivialization,
--   let U := (f ∘ H₁) ⁻¹' t.base_set,
--   refine ⟨U, (t.open_base_set.preimage (hf.continuous.comp H₁.continuous)).mem_nhds
--     ((hf (f (H₁ x)))).mem_to_trivialization_base_set, _⟩,
--   change is_clopen {y : U | H₁ y = H₂ y},
--   have h0 : ∀ y : U, f (H₁ y) = f (H₂ y) := λ y, congr_fun h y,
--   have h1 : ∀ y : U, f (H₁ y) ∈ t.base_set := subtype.prop,
--   have h2 : ∀ y : U, f (H₂ y) ∈ t.base_set := λ y, h0 y ▸ h1 y,
--   have key : ∀ y : U, H₁ y = H₂ y ↔ (t (H₁ y)).2 = (t (H₂ y)).2,
--   { refine λ y, ⟨congr_arg (prod.snd ∘ t), λ m, _⟩,
--     have h0 : f (H₁ y) = f (H₂ y) := congr_fun h y,
--     rw [←t.coe_fst' (h1 y), ←t.coe_fst' (h2 y)] at h0,
--     refine t.inj_on (t.mem_source.mpr (h1 y)) (t.mem_source.mpr (h2 y)) (prod.ext h0 m) },
--   simp_rw [key],
--   haveI := (hf (f (H₁ x))).1,
--   simp only [←t.mem_source] at h1 h2,
--   refine clopen_equalizer_of_discrete
--     (continuous_snd.comp (t.continuous_to_fun.comp_continuous (H₁.2.comp continuous_subtype_coe) h1))