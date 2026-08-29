module

public import SphereSixComplex.Periods.EstablishedFuchsianTorsorDescent
public import SphereSixComplex.Periods.FuchsianCuspNormalization
public import SphereSixComplex.Topology.StandardInfiniteA2PolarPhaseDeck

/-!
# Established phase spreading for the standard infinite `A₂` toric model

This boundary records only the standard toric orbit, deck, and stabilizer compatibility package.
It contains no quotient retraction, homology, Euler-characteristic, or global paper conclusion.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.CuspToricPhaseAction

/-- The positive real complex unit with the same norm as a given complex unit. -/
public def positiveRadialPart (z : ℂˣ) : ℂˣ :=
  Units.mk0 (‖(z : ℂ)‖ : ℂ)
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Units.ne_zero z)))

public theorem positiveRadialPart_re (z : ℂˣ) :
    0 < ((positiveRadialPart z : ℂˣ) : ℂ).re := by
  change 0 < ‖(z : ℂ)‖
  exact norm_pos_iff.mpr (Units.ne_zero z)

public theorem positiveRadialPart_im (z : ℂˣ) :
    ((positiveRadialPart z : ℂˣ) : ℂ).im = 0 := by
  rfl

public theorem norm_positiveRadialPart (z : ℂˣ) :
    ‖((positiveRadialPart z : ℂˣ) : ℂ)‖ = ‖(z : ℂ)‖ := by
  change ‖(‖(z : ℂ)‖ : ℂ)‖ = ‖(z : ℂ)‖
  exact Complex.norm_of_nonneg (norm_nonneg _)

public theorem positiveRadialPart_mul (z w : ℂˣ) :
    positiveRadialPart (z * w) = positiveRadialPart z * positiveRadialPart w := by
  apply Units.ext
  simp [positiveRadialPart]

/-- The coordinatewise positive radial part of the normalized frozen cusp multiplier. -/
public def normalizedCuspPositiveTwist
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) :
    ParameterLattice → DenseTorus :=
  fun lambda i ↦ positiveRadialPart
    (phaseEmbedding (N.phaseCoefficient lambda 0) i)

@[simp]
public theorem normalizedCuspPositiveTwist_zero
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) :
    normalizedCuspPositiveTwist N 0 = 1 := by
  funext i
  simp [normalizedCuspPositiveTwist, positiveRadialPart]

public theorem normalizedCuspPositiveTwist_add
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda mu : ParameterLattice) :
    normalizedCuspPositiveTwist N (lambda + mu) =
      normalizedCuspPositiveTwist N lambda * normalizedCuspPositiveTwist N mu := by
  funext i
  change positiveRadialPart (phaseEmbedding (N.phaseCoefficient (lambda + mu) 0) i) =
    positiveRadialPart (phaseEmbedding (N.phaseCoefficient lambda 0) i) *
      positiveRadialPart (phaseEmbedding (N.phaseCoefficient mu 0) i)
  rw [N.phaseCoefficient_add, map_mul, Pi.mul_apply, positiveRadialPart_mul]

@[simp]
public theorem normalizedCuspPositiveTwist_last
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda : ParameterLattice) :
    normalizedCuspPositiveTwist N lambda 2 = 1 := by
  apply Units.ext
  simp [normalizedCuspPositiveTwist, positiveRadialPart]

public theorem normalizedCuspPositiveTwist_real
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda : ParameterLattice) (i : Fin 3) :
    0 < ((normalizedCuspPositiveTwist N lambda i : ℂˣ) : ℂ).re ∧
      ((normalizedCuspPositiveTwist N lambda i : ℂˣ) : ℂ).im = 0 :=
  ⟨positiveRadialPart_re _, positiveRadialPart_im _⟩

/-- The canonical positive twist has exactly the frozen cusp multiplier's radial norm. -/
public theorem norm_normalizedCuspPositiveTwist
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda : ParameterLattice) (i : Fin 3) :
    ‖((normalizedCuspPositiveTwist N lambda i : ℂˣ) : ℂ)‖ =
      ‖((phaseEmbedding (N.phaseCoefficient lambda 0) i : ℂˣ) : ℂ)‖ :=
  norm_positiveRadialPart _

/-- The polar decomposition already proves surjectivity of the compact phase orbit map. -/
public theorem compactPhaseOrbit_surjective
    (M : Model) (r : ℝ) (P : PolarHoneycombData M r) :
    Function.Surjective (compactPhaseOrbit M r P.positivePart) := by
  intro p
  obtain ⟨phi, hphi⟩ := P.polar_surjective p
  refine ⟨(phi, P.modulus p), ?_⟩
  apply Subtype.ext
  exact hphi

/-- The remaining geometric construction chooses polar coordinates for which compact phase
coordinates are open and the lifted cellular homotopy preserves their stabilizers.  Its deck
correction is reduced to equality of the radial norms of the frozen and positive multipliers. -/
public axiom polarHoneycombPhaseSpreadingGeometry
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ) (hr : 0 < r) :
    Nonempty { P : PolarHoneycombData M r //
      PolarPhaseRadialCompatibility N M r P ∧ PolarPhaseGeometricCore M r P }

/-- The standard polar-honeycomb model can be chosen compatibly with compact phase orbits, the
frozen deck action, and the stabilizers of the positive-part cellular homotopy. -/
public theorem polarHoneycombPhaseSpreadingPackage
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ) (hr : 0 < r) :
    Nonempty (Σ P : PolarHoneycombData M r,
      FrozenLocalCuspPhaseSpreadingData N M r P) := by
  obtain ⟨⟨P, H, G⟩⟩ := polarHoneycombPhaseSpreadingGeometry N M r hr
  exact ⟨⟨P, FrozenLocalCuspPhaseSpreadingData.ofPolarPhaseData H.toDeckLift G⟩⟩

/-- Forgetting the phase-spreading compatibility gives the underlying polar-honeycomb model. -/
public theorem polarHoneycombData (M : Model) (r : ℝ) (hr : 0 < r) :
    Nonempty (PolarHoneycombData M r) := by
  obtain ⟨E⟩ := exists_establishedFuchsianModularParameter
  obtain ⟨F⟩ := establishedExactLiftedModularNegOneFrame E
  let D := establishedFuchsianPeriodLocalData E F
  obtain ⟨N⟩ := FuchsianCuspNormalization.exists_normalizedFuchsianCuspCoordinate E D
  exact Nonempty.map (fun package ↦ package.1)
    (polarHoneycombPhaseSpreadingPackage N M r hr)

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
