import SphereSixComplex.Periods.EstablishedOrbifoldAffineTorsorDescent
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Audit of the analytic descent API

This scratch file records the part of regular-cover descent that is already available in
Mathlib.  It deliberately imports only authoritative project files.  The global affine-torsor
trivialization (a Stein/Cartan-B or additive Cousin theorem) is not assumed below.
-/

open Matrix UpperHalfPlane
open scoped Manifold MatrixGroups

noncomputable section

namespace SphereSixComplex.Periods.AgentAnalyticDescent

open SphereSixComplex.TriangleGroup

/-- The complex representative of the quotient coordinate near a point of the upper half-plane.
Outside the upper half-plane `ofComplex` is an arbitrary extension, which is harmless for local
statements at points of positive imaginary part. -/
def coordinateComplex (C : ExactFuchsianOrbifoldCoordinate) : ℂ → ℂ :=
  C.coordinate ∘ UpperHalfPlane.ofComplex

/-- The exact covering hypothesis supplies a topological local inverse at every regular point. -/
theorem coordinate_isLocalHomeomorphOn_regular
    (C : ExactFuchsianOrbifoldCoordinate) :
    IsLocalHomeomorphOn C.coordinate
      (C.coordinate ⁻¹' (({0, 1} : Set ℂ)ᶜ)) :=
  C.regular_covering.isLocalHomeomorphOn

/-- Concretely, a regular source point lies in the source of an open partial homeomorphism whose
underlying function is the quotient coordinate.  This inverse is only topological. -/
theorem exists_coordinate_openPartialHomeomorph
    (C : ExactFuchsianOrbifoldCoordinate) (z : UpperHalfPlane)
    (hz : C.coordinate z ∈ (({0, 1} : Set ℂ)ᶜ)) :
    ∃ e : OpenPartialHomeomorph UpperHalfPlane ℂ,
      z ∈ e.source ∧ C.coordinate = e :=
  coordinate_isLocalHomeomorphOn_regular C z hz

/-- Holomorphicity of the quotient coordinate in the ambient complex chart. -/
theorem coordinateComplex_analyticAt
    (C : ExactFuchsianOrbifoldCoordinate) (z : UpperHalfPlane) :
    AnalyticAt ℂ (coordinateComplex C) (z : ℂ) := by
  apply DifferentiableOn.analyticAt
      (UpperHalfPlane.mdifferentiable_iff.mp C.coordinate_holomorphic)
  exact UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos

/-- The missing local bridge, isolated as a proposition.  It should follow mathematically from
holomorphicity plus the local injectivity supplied by the covering, but no such theorem is
currently available in Mathlib's one-variable complex API. -/
def RegularCoordinateDerivativeNonzero
    (C : ExactFuchsianOrbifoldCoordinate) : Prop :=
  ∀ z : UpperHalfPlane,
    C.coordinate z ∈ (({0, 1} : Set ℂ)ᶜ) →
      deriv (coordinateComplex C) (z : ℂ) ≠ 0

/-- Once the nonzero-derivative bridge is supplied, Mathlib's analytic inverse theorem descends
analyticity through the quotient coordinate at a regular point. -/
theorem analyticAt_of_comp_coordinateComplex
    (C : ExactFuchsianOrbifoldCoordinate)
    (hderiv : RegularCoordinateDerivativeNonzero C)
    (g : ℂ → ℂ) (z : UpperHalfPlane)
    (hz : C.coordinate z ∈ (({0, 1} : Set ℂ)ᶜ))
    (hg : AnalyticAt ℂ (g ∘ coordinateComplex C) (z : ℂ)) :
    AnalyticAt ℂ g (C.coordinate z) := by
  have h :=
    (analyticAt_comp_iff_of_deriv_ne_zero
      (coordinateComplex_analyticAt C z) (hderiv z hz)).mp hg
  simpa [coordinateComplex, UpperHalfPlane.ofComplex_apply] using h

/-- The same bridge stated at the differentiability level used by the project structures. -/
theorem mdifferentiableAt_of_comp_coordinateComplex
    (C : ExactFuchsianOrbifoldCoordinate)
    (hderiv : RegularCoordinateDerivativeNonzero C)
    (g : ℂ → ℂ) (z : UpperHalfPlane)
    (hz : C.coordinate z ∈ (({0, 1} : Set ℂ)ᶜ))
    (hg : AnalyticAt ℂ (g ∘ coordinateComplex C) (z : ℂ)) :
    MDiffAt g (C.coordinate z) :=
  (analyticAt_of_comp_coordinateComplex C hderiv g z hz hg).differentiableAt.mdifferentiableAt

/-! ## Exact interface for the unavailable global theorem -/

/-- Honest compatibility needed for the cusp normalization.  It says that normalization changes
origins but does not change differences in an affine fibre. -/
def NormalizePreservesDifferences
    (P : OrbifoldAffineLineTorsorDescentProblem) : Prop :=
  ∀ z u v, P.cuspNormalize z u - P.cuspNormalize z v = u - v

/-- The substantive output of applying Cartan B/additive Cousin separately on the two affine
quotient charts.  The last two fields record the growth control at the completed cusp in the
unnormalized affine fibre; normalized boundedness is derived below. -/
structure HolomorphicChartSeed (P : OrbifoldAffineLineTorsorDescentProblem) where
  sectionZero : UpperHalfPlane → ℂ
  sectionInfinity : UpperHalfPlane → ℂ
  sectionZero_holomorphic : MDiff sectionZero
  sectionInfinity_holomorphic : ∀ z, P.quotient.coordinate z ≠ 0 →
    MDiffAt sectionInfinity z
  sectionZero_one : ∀ z,
    sectionZero (fuchsianSourceAction g₁ • z) =
      P.affineOne z (sectionZero z)
  sectionZero_two : ∀ z,
    sectionZero (fuchsianSourceAction g₂ • z) =
      P.affineTwo z (sectionZero z)
  sectionInfinity_one : ∀ z, P.quotient.coordinate z ≠ 0 →
    sectionInfinity (fuchsianSourceAction g₁ • z) =
      P.affineOne z (sectionInfinity z)
  sectionInfinity_two : ∀ z, P.quotient.coordinate z ≠ 0 →
    sectionInfinity (fuchsianSourceAction g₂ • z) =
      P.affineTwo z (sectionInfinity z)
  cuspCorrection : UpperHalfPlane → ℂ
  sectionInfinity_sub_cusp : ∀ z, z ∈ fuchsianCuspRegion →
    sectionInfinity z - P.cuspSection z = cuspCorrection z
  cuspCorrection_bounded : BoundedOn cuspCorrection fuchsianCuspRegion

/-- The second local analytic obligation: the homogeneous mismatch of the two chart seeds descends
and extends holomorphically across both finite orbifold values.  Regular-covering descent plus the
nonzero-derivative bridge handles ordinary points; the extension at `0` and `1` needs the exact
branch/divisibility argument. -/
structure HolomorphicOverlapDescent
    (P : OrbifoldAffineLineTorsorDescentProblem) (S : HolomorphicChartSeed P) where
  overlapCocycle : ℂ → ℂ
  overlapCocycle_holomorphic : HolomorphicOnPuncturedPlane overlapCocycle
  section_mismatch : ∀ z, P.quotient.coordinate z ≠ 0 →
    S.sectionZero z - S.sectionInfinity z =
      overlapCocycle (P.quotient.coordinate z) * P.frameZero z

/-- A small boundedness lemma, included so the cusp conclusion below is genuinely derived rather
than hidden in the chart seed. -/
theorem boundedOn_add {f g : UpperHalfPlane → ℂ} {s : Set UpperHalfPlane}
    (hf : BoundedOn f s) (hg : BoundedOn g s) :
    BoundedOn (fun z ↦ f z + g z) s := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf + Cg, add_nonneg hCf hCg, ?_⟩
  intro z hz
  exact (norm_add_le (f z) (g z)).trans (add_le_add (hf z hz) (hg z hz))

/-- Compatibility of normalization turns the seed's ordinary affine correction bound into the
normalized cusp bound required by `TwoChartSections`. -/
theorem chartSeed_normalized_cusp_bounded
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (hNormalize : NormalizePreservesDifferences P)
    (S : HolomorphicChartSeed P) :
    BoundedOn (fun z ↦ P.cuspNormalize z (S.sectionInfinity z))
      fuchsianCuspRegion := by
  have hsum :
      BoundedOn
        (fun z ↦ P.cuspNormalize z (P.cuspSection z) + S.cuspCorrection z)
        fuchsianCuspRegion :=
    boundedOn_add P.cuspSection_normalized_bounded S.cuspCorrection_bounded
  obtain ⟨C, hC, hsum⟩ := hsum
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hdiff := hNormalize z (S.sectionInfinity z) (P.cuspSection z)
  have hcorr := S.sectionInfinity_sub_cusp z hz
  change ‖P.cuspNormalize z (S.sectionInfinity z)‖ ≤ C
  rw [show P.cuspNormalize z (S.sectionInfinity z) =
      P.cuspNormalize z (P.cuspSection z) + S.cuspCorrection z by
    rw [← hcorr]
    linear_combination hdiff]
  simpa only using hsum z hz

/-- The exact assembly step.  All fields other than normalized cusp boundedness are projections
from the two substantive analytic interfaces; cusp boundedness is derived from normalization
compatibility. -/
theorem twoChartSections_of_analytic_interfaces
    (P : OrbifoldAffineLineTorsorDescentProblem)
    (hNormalize : NormalizePreservesDifferences P)
    (S : HolomorphicChartSeed P)
    (D : HolomorphicOverlapDescent P S) :
    Nonempty P.TwoChartSections := by
  refine ⟨{
    sectionZero := S.sectionZero
    sectionInfinity := S.sectionInfinity
    sectionZero_holomorphic := S.sectionZero_holomorphic
    sectionInfinity_holomorphic := S.sectionInfinity_holomorphic
    sectionZero_one := S.sectionZero_one
    sectionZero_two := S.sectionZero_two
    sectionInfinity_one := S.sectionInfinity_one
    sectionInfinity_two := S.sectionInfinity_two
    overlapCocycle := D.overlapCocycle
    overlapCocycle_holomorphic := D.overlapCocycle_holomorphic
    section_mismatch := D.section_mismatch
    sectionInfinity_normalized_cusp_bounded :=
      chartSeed_normalized_cusp_bounded P hNormalize S }⟩

/-- Precise Cartan-B/additive-Cousin existence statement still missing from Mathlib.  This is only
a proposition naming the theorem; it is neither an axiom nor an inhabitant. -/
def HolomorphicAffineChartTriviality : Prop :=
  ∀ P : OrbifoldAffineLineTorsorDescentProblem,
    NormalizePreservesDifferences P → Nonempty (HolomorphicChartSeed P)

/-- Precise quotient-analyticity and orbifold-removability statement still needed after the chart
sections have been constructed.  Again this only names the theorem. -/
def HolomorphicMismatchDescentExistence : Prop :=
  ∀ (P : OrbifoldAffineLineTorsorDescentProblem) (S : HolomorphicChartSeed P),
    Nonempty (HolomorphicOverlapDescent P S)

/-!
The preceding results solve only the *local regular-covering* part.  Constructing either affine
chart section requires the following genuinely global assertion: a holomorphic affine cocycle,
whose finite stabilizer and cusp restrictions admit the recorded local primitives, is a
coboundary on each of the two quotient charts.  Equivalently, the relevant sheaf of homogeneous
sections must have vanishing first cohomology on each Stein chart.  Mathlib has an abstract sheaf
cohomology/Cech-complex API.  Its `smoothSheaf` can be specialized to complex scalar and may serve
as a model for holomorphic functions after additional regularity bridges, but there is no
coherent-analytic-module theory, Stein-space API, Cartan theorem B, or additive Cousin theorem
from which the required vanishing assertion can be instantiated.
-/

#print axioms coordinate_isLocalHomeomorphOn_regular
#print axioms coordinateComplex_analyticAt
#print axioms analyticAt_of_comp_coordinateComplex
#print axioms mdifferentiableAt_of_comp_coordinateComplex
#print axioms chartSeed_normalized_cusp_bounded
#print axioms twoChartSections_of_analytic_interfaces

end SphereSixComplex.Periods.AgentAnalyticDescent
