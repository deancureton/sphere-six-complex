module

public import SphereSixComplex.Topology.SimplicialSixSphereTopHomologyKernel
public import SphereSixComplex.Topology.BoundarySevenRealizationInjective
public import SphereSixComplex.Topology.SixSphereDegreeComparison
public import Mathlib.GroupTheory.Perm.Fin

/-!
# The antipodal degree and the cyclic boundary model

This file isolates the remaining geometric input in the degree calculation.  The cyclic
permutation of the eight barycentric coordinates is an explicit self-homeomorphism of the
ordinary boundary of the seven-simplex, and it is an odd permutation.  Conjugating it by the
constructed boundary--sphere homeomorphism gives a completely concrete self-map of `S⁶`.

The final theorem below shows that the desired assertion for every choice of top-homology
orientation is equivalent to the orientation-free assertion that the analytic antipodal map
induces negation on integral top homology.  It also gives the exact two-input reduction through
the cyclic boundary model.  What is not available in Mathlib is the naturality theorem which
identifies this unordered vertex permutation with its action on the ordered simplicial boundary;
an arbitrary permutation of `Fin 8` is not a morphism of the representable simplicial set
`Delta[7]`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap Set Simplicial

namespace SphereSixComplex

/-- For a bijection of the vertex set, the induced affine map just reindexes barycentric
coordinates. -/
public theorem stdSimplex_map_equiv_apply
    {n : ℕ} (sigma : Equiv.Perm (Fin n)) (w : stdSimplex ℝ (Fin n)) (j : Fin n) :
    stdSimplex.map sigma w j = w (sigma.symm j) := by
  classical
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have hfiber : (Finset.univ.filter fun i : Fin n ↦ sigma i = j) =
      {sigma.symm j} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact sigma.eq_symm_apply.symm
  rw [hfiber]
  simp

/-- A permutation of vertices acts affinely by a homeomorphism of the whole standard simplex. -/
public noncomputable def stdSimplexPermHomeomorph
    {n : ℕ} (sigma : Equiv.Perm (Fin n)) :
    stdSimplex ℝ (Fin n) ≃ₜ stdSimplex ℝ (Fin n) where
  toFun := stdSimplex.map sigma
  invFun := stdSimplex.map sigma.symm
  left_inv w := by
    rw [stdSimplex.map_comp_apply]
    simp only [Equiv.symm_comp_self, stdSimplex.map_id_apply]
  right_inv w := by
    rw [stdSimplex.map_comp_apply]
    simp only [Equiv.self_comp_symm, stdSimplex.map_id_apply]
  continuous_toFun := stdSimplex.continuous_map sigma
  continuous_invFun := stdSimplex.continuous_map sigma.symm

/-- The affine vertex-permutation homeomorphism preserves the topological boundary. -/
public noncomputable def standardSimplexBoundaryPermHomeomorph
    {n : ℕ} (sigma : Equiv.Perm (Fin (n + 1))) :
    StandardSimplexBoundary n ≃ₜ StandardSimplexBoundary n :=
  (stdSimplexPermHomeomorph sigma).subtype
    (p := fun w : stdSimplex ℝ (Fin (n + 1)) ↦ ∃ i, w i = 0)
    (q := fun w : stdSimplex ℝ (Fin (n + 1)) ↦ ∃ i, w i = 0)
    (fun w ↦ by
      constructor
      · rintro ⟨i, hi⟩
        refine ⟨sigma i, ?_⟩
        change stdSimplex.map sigma w (sigma i) = 0
        rw [stdSimplex_map_equiv_apply, sigma.symm_apply_apply]
        exact hi
      · rintro ⟨j, hj⟩
        refine ⟨sigma.symm j, ?_⟩
        change stdSimplex.map sigma w j = 0 at hj
        rw [stdSimplex_map_equiv_apply] at hj
        exact hj)

/-- The eight-cycle `(0 1 ... 7)` acting on the ordinary boundary of the seven-simplex. -/
public noncomputable def boundarySevenCyclicHomeomorph :
    StandardSimplexBoundary 7 ≃ₜ StandardSimplexBoundary 7 :=
  standardSimplexBoundaryPermHomeomorph (finRotate 8)

/-- The cyclic boundary map, transported to the project's standard six-sphere. -/
public noncomputable def cyclicBoundarySphereHomeomorph : SixSphere ≃ₜ SixSphere :=
  standardSimplexBoundarySevenHomeomorphSixSphere.symm.trans
    (boundarySevenCyclicHomeomorph.trans
      standardSimplexBoundarySevenHomeomorphSixSphere)

/-- The transported cyclic boundary homeomorphism as a bundled continuous map. -/
public noncomputable def cyclicBoundarySphereMap : C(SixSphere, SixSphere) :=
  ⟨cyclicBoundarySphereHomeomorph, cyclicBoundarySphereHomeomorph.continuous⟩

/-- The eight-cycle has sign `-1`. -/
public theorem boundarySevenCyclicPermutation_sign :
    Equiv.Perm.sign (finRotate 8) = -1 := by
  rw [sign_finRotate]
  change ((-1 : ℤˣ) ^ 7) = -1
  simp [pow_succ]

/-- The orientation-free formulation of the missing antipodal calculation. -/
public def SixSphereAntipodalActsByNegation : Prop :=
  sixSphereTopIntegralHomologyMap
      OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun =
    -AddMonoidHom.id (IntegralSingularHomology 6 SixSphere)

/-- Negation on top homology gives degree `-1` for every choice of generator. -/
public theorem sixSphere_antipodalDegree_of_actsByNegation
    (h : SixSphereAntipodalActsByNegation)
    (orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ) :
    sixSphereHomologicalDegree orientation
      OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun = -1 := by
  rw [sixSphereHomologicalDegree, h]
  change orientation (-orientation.symm 1) = -1
  rw [orientation.map_neg, orientation.apply_symm_apply]

/-- Conversely, degree `-1` for one orientation forces the induced endomorphism itself to be
negation.  Thus the antipodal input is independent of all choices of generator. -/
public theorem sixSphere_antipodalActsByNegation_of_degree
    (orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ)
    (hdegree : sixSphereHomologicalDegree orientation
      OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun = -1) :
    SixSphereAntipodalActsByNegation := by
  let H := IntegralSingularHomology 6 SixSphere
  let fH : H →+ H := sixSphereTopIntegralHomologyMap
    OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun
  let fZ : ℤ →+ ℤ := orientation.toAddMonoidHom.comp
    (fH.comp orientation.symm.toAddMonoidHom)
  have hf (z : ℤ) : orientation (fH (orientation.symm z)) = -z := by
    change fZ z = -z
    rw [intAddHom_apply_eq_mul_apply_one]
    change z * sixSphereHomologicalDegree orientation
      OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun = -z
    rw [hdegree]
    simp
  unfold SixSphereAntipodalActsByNegation
  apply AddMonoidHom.ext
  intro x
  apply orientation.injective
  have hx := hf (orientation x)
  rw [orientation.symm_apply_apply] at hx
  simpa using hx

/-- The analytic antipodal map has degree `-1` for every orientation exactly when it acts by
negation on top integral homology. -/
public theorem sixSphere_antipodalDegree_iff_actsByNegation
    (orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ) :
    (sixSphereHomologicalDegree orientation
        OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun = -1) ↔
      SixSphereAntipodalActsByNegation := by
  constructor
  · intro h
    exact sixSphere_antipodalActsByNegation_of_degree orientation h
  · intro h
    exact sixSphere_antipodalDegree_of_actsByNegation h orientation

/-- It is enough to compute the antipodal degree using one generator: the answer `-1` is then
forced for every other additive orientation. -/
public theorem sixSphere_antipodalDegree_allOrientations_of_one
    (orientation₀ : IntegralSingularHomology 6 SixSphere ≃+ ℤ)
    (h₀ : sixSphereHomologicalDegree orientation₀
      OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun = -1)
    (orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ) :
    sixSphereHomologicalDegree orientation
      OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun = -1 :=
  sixSphere_antipodalDegree_of_actsByNegation
    (sixSphere_antipodalActsByNegation_of_degree orientation₀ h₀) orientation

/-- Exact reduction through the explicit odd cyclic boundary homeomorphism.  The first input is
the finite permutation action after comparison; the second is the geometric homotopy from the
transported cyclic map to the analytic antipodal map. -/
public theorem sixSphere_antipodalDegree_of_cyclicBoundaryModel
    (hcyclic : sixSphereTopIntegralHomologyMap cyclicBoundarySphereMap =
      -AddMonoidHom.id (IntegralSingularHomology 6 SixSphere))
    (hhomotopy :
      OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun.Homotopic
        cyclicBoundarySphereMap)
    (orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ) :
    sixSphereHomologicalDegree orientation
      OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun = -1 := by
  apply sixSphere_antipodalDegree_of_actsByNegation
  unfold SixSphereAntipodalActsByNegation
  rw [sixSphereTopIntegralHomologyMap_eq_of_homotopic hhomotopy]
  exact hcyclic

/-- A calculation of the cyclic map on one transported generator, together with the explicit
geometric homotopy, implies the antipodal result for every possible generator.  This is the form
needed by `sixSphereDegreeTheory_of_boundaryComparison`. -/
public theorem sixSphere_antipodalDegree_all_of_cyclicBoundaryDegree
    (orientation₀ : IntegralSingularHomology 6 SixSphere ≃+ ℤ)
    (hcyclic : sixSphereHomologicalDegree orientation₀
      cyclicBoundarySphereMap = -1)
    (hhomotopy :
      OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun.Homotopic
        cyclicBoundarySphereMap)
    (orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ) :
    sixSphereHomologicalDegree orientation
      OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun = -1 := by
  apply sixSphere_antipodalDegree_allOrientations_of_one orientation₀
  exact (sixSphereHomologicalDegree_eq_of_homotopic orientation₀ hhomotopy).trans hcyclic

end SphereSixComplex
