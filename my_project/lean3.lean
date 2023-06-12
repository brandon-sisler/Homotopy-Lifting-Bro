import Mathlib.Topology.Covering

variable {α : Type}{E X : Type α} [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (s : Set X)

/-- A point `x : X` is evenly covered by `f : E → X` if `x` has an evenly covered neighborhood. -/

--`def IsEvenlyCovered (x : X) (I : Type _) [TopologicalSpace I] `:=
--  `DiscreteTopology I ∧ ∃ t : Trivialization I f, x ∈ t.baseSet`


namespace is_covering_map
lemma mk (F : X → Type*) [Π x, topological_space (F x)] [hF : Π x, discrete_topology (F x)]
  (e : Π x, trivialization (F x) f) (h : ∀ x, x ∈ (e x).base_set) : is_covering_map f :=
is_covering_map_iff_is_covering_map_on_univ.mpr
  (is_covering_map_on.mk f set.univ F (λ x hx, e x) (λ x hx, h x))
variables {f}
protected lemma continuous (hf : is_covering_map f) : continuous f :=
continuous_iff_continuous_on_univ.mpr hf.is_covering_map_on.continuous_on
protected lemma is_locally_homeomorph (hf : is_covering_map f) : is_locally_homeomorph f :=
is_locally_homeomorph_iff_is_locally_homeomorph_on_univ.mpr
  hf.is_covering_map_on.is_locally_homeomorph_on
protected lemma is_open_map (hf : is_covering_map f) : is_open_map f :=
hf.is_locally_homeomorph.is_open_map
protected lemma quotient_map (hf : is_covering_map f) (hf' : function.surjective f) :
  quotient_map f :=
hf.is_open_map.to_quotient_map hf.continuous hf'

noncomputable def to_homeomorph (hf : is_covering_map f)
  (h : function.bijective f) : homeomorph E X :=
homeomorph.homeomorph_of_continuous_open (equiv.of_bijective f h) hf.continuous hf.is_open_map

open_locale cardinal

lemma is_locally_constant_card (hf : is_covering_map f) :
  is_locally_constant (λ x, #(f ⁻¹' {x})) :=
(is_locally_constant.iff_exists_open _).2 $ λ x, let ⟨t, ht⟩ := (hf x).2 in
  ⟨_, t.open_base_set, ht, λ y hy, (t.preimage_singleton_homeomorph hy).to_equiv.cardinal_eq⟩

end is_covering_map

variables {f}
Expand All
	@@ -157,8 +171,84 @@ protected lemma is_fiber_bundle.is_covering_map {F : Type*} [topological_space F
  is_covering_map f :=
is_covering_map.mk f (λ x, F) (λ x, classical.some (hf x)) (λ x, classical.some_spec (hf x))

open_locale unit_interval

lemma clopen_set_intersect_connected_components_whole_set (Y: Type*) [topological_space Y]
  (S : set Y) (hS : is_clopen S) (w : ∀ x : Y, ∃ y ∈ connected_component x, y ∈ S) :
  S = set.univ :=
set.eq_univ_of_forall $ λ x, let ⟨y, hy, h⟩ := w x in
  hS.connected_component_subset h (connected_component_eq hy ▸ mem_connected_component)

open_locale topological_space

lemma is_open_inter_of_coe_preim {X : Type*} [topological_space X] (s t : set X) (hs : is_open s)
  (h : is_open ((coe : s → X) ⁻¹' t)) : is_open (t ∩ s) :=
let ⟨a, b, c⟩ := inducing_coe.is_open_iff.mp h in
  subtype.preimage_coe_eq_preimage_coe_iff.mp c ▸ b.inter hs

lemma is_open_of_is_open_coe (Y:Type*) [topological_space Y] (A: set Y)
(hA : ∀ x : Y, ∃ (U : set Y) (hU : U ∈ 𝓝 x), is_open ((coe : U → Y) ⁻¹' A)) : is_open A :=
is_open_iff_forall_mem_open.mpr (λ x hx, let ⟨U, hU1, hU2⟩ := hA x,
  ⟨V, hV1, hV2, hV3⟩ := mem_nhds_iff.mp hU1 in ⟨A ∩ V, set.inter_subset_left A V,
    is_open_inter_of_coe_preim V A hV2 ((continuous_inclusion hV1).is_open_preimage _ hU2), hx, hV3⟩)
 Check failure on line 193 in src/topology/covering.lean

GitHub Actions
/ Lint style

ERR_LIN: Line has more than 100 characters

lemma is_closed_of_is_closed_coe (Y:Type*) [topological_space Y] (A: set Y)
(hA : ∀ x : Y, ∃ (U : set Y) (hU : U ∈ 𝓝 x), is_closed ((coe : U → Y) ⁻¹' A)) : is_closed A :=
 ⟨ is_open_of_is_open_coe Y Aᶜ (λ x, let ⟨U, hU,hN⟩ := hA x in ⟨ U,  hU , hN.1 ⟩) ⟩

lemma is_clopen_of_is_clopen_coe (Y:Type*) [topological_space Y] (A: set Y)
(hA : ∀ x : Y, ∃ (U : set Y) (hU : U ∈ 𝓝 x), is_clopen ((coe : U → Y) ⁻¹' A)) : is_clopen A :=
⟨is_open_of_is_open_coe  Y A (λ x, let  ⟨ z,hz,hhz⟩:= hA x in ⟨ z,hz,hhz.1⟩  ) ,
 is_closed_of_is_closed_coe  Y A (λ x, let  ⟨ z,hz,hhz⟩:= hA x in ⟨ z,hz,hhz.2⟩  )⟩

theorem clopen_equalizer_of_discrete {X Y : Type*} [topological_space X] [topological_space Y]
  [discrete_topology Y] {f g : X → Y} (hf : continuous f) (hg : continuous g) :
  is_clopen {x : X | f x = g x} := (is_clopen_discrete (set.diagonal Y)).preimage (hf.prod_mk hg)


lemma tautology : true := sorry
 Check warning on line 209 in src/topology/covering.lean

GitHub Actions
/ Build mathlib

/home/lean/actions-runner/_work/mathlib/mathlib/src/topology/covering.lean:209:0:
declaration 'tautology' uses sorry

theorem uniqueness_of_homotopy_lifting (Y : Type*) [topological_space Y] (hf : is_covering_map f)
  (H₁ H₂ : continuous_map Y E) (h : f ∘ H₁ = f ∘ H₂)
  (hC : ∀ x : Y, ∃ y ∈ connected_component x, H₁ y = H₂ y) :
  H₁ = H₂ :=
begin
  refine fun_like.ext H₁ H₂ (set.eq_univ_iff_forall.mp
    (clopen_set_intersect_connected_components_whole_set _ _
    (is_clopen_of_is_clopen_coe _ _ (λ x, _)) hC)),
  let t := (hf (f (H₁ x))).to_trivialization,
  let U := (f ∘ H₁) ⁻¹' t.base_set,
  refine ⟨U, (t.open_base_set.preimage (hf.continuous.comp H₁.continuous)).mem_nhds
    ((hf (f (H₁ x)))).mem_to_trivialization_base_set, _⟩,
  change is_clopen {y : U | H₁ y = H₂ y},
  have h0 : ∀ y : U, f (H₁ y) = f (H₂ y) := λ y, congr_fun h y,
  have h1 : ∀ y : U, f (H₁ y) ∈ t.base_set := subtype.prop,
  have h2 : ∀ y : U, f (H₂ y) ∈ t.base_set := λ y, h0 y ▸ h1 y,
  have key : ∀ y : U, H₁ y = H₂ y ↔ (t (H₁ y)).2 = (t (H₂ y)).2,
  { refine λ y, ⟨congr_arg (prod.snd ∘ t), λ m, _⟩,
    have h0 : f (H₁ y) = f (H₂ y) := congr_fun h y,
    rw [←t.coe_fst' (h1 y), ←t.coe_fst' (h2 y)] at h0,
    refine t.inj_on (t.mem_source.mpr (h1 y)) (t.mem_source.mpr (h2 y)) (prod.ext h0 m) },
  simp_rw [key],
  haveI := (hf (f (H₁ x))).1,
  simp only [←t.mem_source] at h1 h2,
  refine clopen_equalizer_of_discrete
    (continuous_snd.comp (t.continuous_to_fun.comp_continuous (H₁.2.comp continuous_subtype_coe) h1))
 Check failure on line 236 in src/topology/covering.lean

GitHub Actions
/ Lint style

ERR_LIN: Line has more than 100 characters
    (continuous_snd.comp (t.continuous_to_fun.comp_continuous (H₂.2.comp continuous_subtype_coe) h2)),
 Check failure on line 237 in src/topology/covering.lean

GitHub Actions
/ Lint style

ERR_LIN: Line has more than 100 characters
end