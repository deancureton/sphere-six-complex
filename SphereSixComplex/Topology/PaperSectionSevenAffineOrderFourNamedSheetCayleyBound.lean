module

public import SphereSixComplex.Topology.PaperSectionSevenAffineOrderFourEndpointRealPeriodIdentityProof

/-!
# The remaining named-sheet issue for the order-four endpoint

The proved overlap inclusion places a regular-deck translate of the named radial lift in the
selected Cayley collar.  This module extracts that translate explicitly.  The remaining step is
to identify it with the identity sheet selected by the pinned strip lift.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

/-- The current overlap and radial-lift APIs prove the Cayley bound after a regular deck
translation.  This is the strongest sheet-sensitive conclusion available from the selected
affine-disc inclusion. -/
public theorem exists_regularDeck_namedOrderFourRadialBase_cayley_lt
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) :
    ∃ g : Delta,
      ‖(orderFourCayleyHomeomorph
        (fuchsianSourceAction g •
          (A.sectionSevenAffineOrderFourRadialBaseLift
            (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
        A.starSeparation.orderFour.radius := by
  let u := A.sectionSevenAffineOrderFourDiscOverlapEndpoint x
  let z := A.orderFourOverlapCollarHomeomorph u
  let q := Quotient.out z
  have hq : Quotient.mk _ q = z := Quotient.out_eq z
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let qreg : RegularTotalSpace A.periods :=
    orderFourCollarToRegular A.periods hproper
      A.starSeparation.orderFour.sourceData
      (orderFourPuncturedCollarGaugeEquiv A.periods
        A.starSeparation.orderFour.radius q)
  have hstar : A.starToCentral 2 z =
      A.centralQuotientProjection
        (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1 := by
    rw [show z = A.orderFourOverlapCollarHomeomorph u by rfl]
    rw [A.starToCentral_orderFourOverlapCollarHomeomorph]
    rw [A.centralQuotientProjection_namedDiscLiftPoint x]
    apply congrArg A.sectionSevenEllipticCentralImageHomeomorph
    apply Subtype.ext
    exact A.sectionSevenAffineOrderFourDiscOverlapEndpoint_val x
  have hcentral : A.centralQuotientProjection qreg =
      A.centralQuotientProjection
        (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1 := by
    rw [← A.orderFourStarToCentral_mk q, hq]
    exact hstar
  let _ := regularFamilyDeckAction A.periods
  rw [centralQuotientProjection.eq_def] at hcentral
  have hrel := Quotient.exact hcentral
  change MulAction.orbitRel Delta _ qreg
    (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1 at hrel
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  change regularFamilyDeckMap A.periods g
      (A.sectionSevenAffineOrderFourNamedDiscLiftPoint x).1 = qreg at hg
  refine ⟨g, ?_⟩
  have hbase : fuchsianSourceAction g •
      (A.sectionSevenAffineOrderFourRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1 =
      (regularTotalSpaceBase A.periods qreg).1 := by
    rw [← A.regularTotalSpaceBase_namedDiscLiftPoint x]
    rw [← hg, regularTotalSpaceBase_familyDeckMap]
    rfl
  rw [hbase]
  have hqmem := q.property
  change 0 < orderFourFamilyRadius A.periods q.1 ∧
    orderFourFamilyRadius A.periods q.1 <
      A.starSeparation.orderFour.radius at hqmem
  have hqradius : ‖(orderFourCayleyHomeomorph
      (familyTotalSpaceBase A.periods q.1) : ℂ)‖ <
      A.starSeparation.orderFour.radius := by
    simpa only [orderFourFamilyRadius.eq_def] using hqmem.2
  have hqregbase : (regularTotalSpaceBase A.periods qreg).1 =
      familyTotalSpaceBase A.periods q.1 := by
    have hinc := regularFamilyInclusion_orderFourCollarToRegular A.periods hproper
      A.starSeparation.orderFour.sourceData
      (orderFourPuncturedCollarGaugeEquiv A.periods
        A.starSeparation.orderFour.radius q)
    have hb := congrArg (familyTotalSpaceBase A.periods) hinc
    change familyTotalSpaceBase A.periods
        (regularFamilyInclusion A.periods qreg) =
      familyTotalSpaceBase A.periods
        (orderFourPrincipalGaugeEquiv A.periods q.1) at hb
    rw [familyTotalSpaceBase_regularFamilyInclusion] at hb
    exact hb.trans (familyTotalSpaceBase_orderFourPrincipalGauge A.periods q.1)
  rw [hqregbase]
  exact hqradius

/-- The smallest equality needed to transfer the selected-collar bound from a deck translate to
the named radial lift is equality of their order-four Cayley norms. -/
public theorem namedOrderFourRadialBase_cayley_lt_of_deck_cayley_norm_eq
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) (g : Delta)
    (hsmall : ‖(orderFourCayleyHomeomorph
      (fuchsianSourceAction g •
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
        A.starSeparation.orderFour.radius)
    (hnorm : ‖(orderFourCayleyHomeomorph
        (fuchsianSourceAction g •
          (A.sectionSevenAffineOrderFourRadialBaseLift
            (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ =
      ‖(orderFourCayleyHomeomorph
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖) :
    ‖(orderFourCayleyHomeomorph
      (A.sectionSevenAffineOrderFourRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
      A.starSeparation.orderFour.radius := by
  rw [hnorm] at hsmall
  exact hsmall

/-- Identity-sheet normalization implies the required Cayley-norm equality, hence the bound. -/
public theorem namedOrderFourRadialBase_cayley_lt_of_deck_fixed
    (A : PaperAnalyticData) (x : A.SectionSevenAffineMarkedBand) (g : Delta)
    (hsmall : ‖(orderFourCayleyHomeomorph
      (fuchsianSourceAction g •
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1) : ℂ)‖ <
        A.starSeparation.orderFour.radius)
    (hfixed : fuchsianSourceAction g •
        (A.sectionSevenAffineOrderFourRadialBaseLift
          (A.sectionSevenAffineBandStripCoordinate x)).1 =
      (A.sectionSevenAffineOrderFourRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1) :
    ‖(orderFourCayleyHomeomorph
      (A.sectionSevenAffineOrderFourRadialBaseLift
        (A.sectionSevenAffineBandStripCoordinate x)).1 : ℂ)‖ <
      A.starSeparation.orderFour.radius := by
  apply A.namedOrderFourRadialBase_cayley_lt_of_deck_cayley_norm_eq x g hsmall
  rw [hfixed]

end SphereSixComplex.Geometry.PaperAnalyticData

end
