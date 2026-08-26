module

public import SphereSixComplex.Geometry.OpenEmbeddingStarGluing
public import SphereSixComplex.Geometry.PaperCollarSeparation
public import SphereSixComplex.Geometry.PaperCentralFamilyTopology
import all SphereSixComplex.Geometry.CuspPuncturedCollarBridge

/-!
# The concrete four-piece open-embedding star

This module packages the cusp and two elliptic collars, at the simultaneously separated radii,
as the common-source open embeddings used by the topological star gluing.
-/

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open TorusFamily AnalyticTorusFamily GlobalTorusFamily ComplexTorus
open EllipticLocalCoordinates EllipticCayleyHomeomorph
open CuspFilling CuspLocalPhaseAction
open CuspPuncturedCollarBridge EllipticPuncturedCollarGaugeHomeomorph
open EstablishedFuchsianCuspNeighborhood
open EllipticVaryingFamilyQuotient EllipticLogarithmicGaugeDescent
open EllipticLinearCollarGlobalDescent
open EllipticWholeFiberCompactCover
open EquivariantQuotientHomeomorph
open CuspPeriodExpansion
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness

noncomputable section

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- The order-three ambient collar graph is closed.  Compact annuli control the punctured part,
and base-orbit separation controls the collapsed central fiber. -/
public theorem orderThreePuncturedCollarPairRange_isClosed
    {r : ℝ} (hr : r < 1)
    (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    IsClosed (Set.range (fun Q : Quotient (restrictedOrbitRel
      (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)) =>
      (A.orderThreePuncturedCollarToCentralFamily D Q,
        A.orderThreePuncturedCollarToFilling r Q))) := by
  let _ : T2Space A.CentralFamily := A.centralFamily_t2
  let _ : T2Space (A.OrderThreeVaryingFilling r) := A.orderThreeFilling_t2 r
  apply isClosed_range_prod_of_compact_radial_annuli
    (toCentral := A.orderThreePuncturedCollarToCentralFamily D)
    (toFilling := A.orderThreePuncturedCollarToFilling r)
    (sourceRadius := A.orderThreePuncturedCollarRadius r)
    (fillingRadius := A.orderThreeFillingRadius r) (r := r)
  · exact A.orderThreeFillingRadius_continuous r
  · exact A.orderThreeFillingRadius_nonneg r
  · exact A.orderThreeFillingRadius_lt r
  · exact A.orderThreeFillingRadius_puncturedCollarToFilling r
  · intro s t hs ht
    exact A.orderThreePuncturedCollarPairClosedAnnulus_isCompact hs ht hr D
  · exact A.exists_orderThreeCentralNeighborhood_avoids_small_collar D

/-- The order-four ambient collar graph is closed by the same radial-end argument. -/
public theorem orderFourPuncturedCollarPairRange_isClosed
    {r : ℝ} (hr : r < 1)
    (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    IsClosed (Set.range (fun Q : Quotient (restrictedOrbitRel
      (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)) =>
      (A.orderFourPuncturedCollarToCentralFamily D Q,
        A.orderFourPuncturedCollarToFilling r Q))) := by
  let _ : T2Space A.CentralFamily := A.centralFamily_t2
  let _ : T2Space (A.OrderFourVaryingFilling r) := A.orderFourFilling_t2 r
  apply isClosed_range_prod_of_compact_radial_annuli
    (toCentral := A.orderFourPuncturedCollarToCentralFamily D)
    (toFilling := A.orderFourPuncturedCollarToFilling r)
    (sourceRadius := A.orderFourPuncturedCollarRadius r)
    (fillingRadius := A.orderFourFillingRadius r) (r := r)
  · exact A.orderFourFillingRadius_continuous r
  · exact A.orderFourFillingRadius_nonneg r
  · exact A.orderFourFillingRadius_lt r
  · exact A.orderFourFillingRadius_puncturedCollarToFilling r
  · intro s t hs ht
    exact A.orderFourPuncturedCollarPairClosedAnnulus_isCompact hs ht hr D
  · exact A.exists_orderFourCentralNeighborhood_avoids_small_collar D

public noncomputable abbrev starCuspWitness := A.actualPuncturedCuspWitness
public noncomputable abbrev starSeparation := A.collarSeparationData

/-- On the normalized additive cover, the descended punctured-cusp radius is exactly `|q|`. -/
public theorem puncturedLocalCuspRadius_additiveCuspRadiusToQuotient
    (a : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    puncturedLocalCuspRadius A.starCuspWitness
        (additiveCuspRadiusToPuncturedLocalCuspQuotient A.starCuspWitness a) =
      ‖cuspQ a.1.2‖ := by
  rw [additiveCuspRadiusToPuncturedLocalCuspQuotient,
    puncturedLocalCuspRadius_mk]
  rw [show ((additiveToPuncturedLocalHomeomorph A.toricModel
      A.starCuspWitness.localWitness.radius (Quotient.mk _ a)).1 :
        LocalCarrier A.toricModel A.starCuspWitness.localWitness.radius) =
      localCuspExponentialPoint A.toricModel A.starCuspWitness.localWitness.radius
        a.1.1 a.1.2 (mem_ball_zero_iff.mpr a.2) from
    additiveToPuncturedLocalHomeomorph_mk A.toricModel
      A.starCuspWitness.localWitness.radius a]
  rw [localCuspExponentialPoint_t]

/-- Forgetting the fibre coordinate of an additive cusp point gives the orbit of its normalized
source lift. -/
public theorem centralBaseOrbit_puncturedCusp_additiveCuspRadiusToQuotient
    (a : additiveCuspRadiusCover A.starCuspWitness.localWitness.radius) :
    A.centralBaseOrbit
        (puncturedLocalCuspQuotientMap A.starCuspWitness
          (additiveCuspRadiusToPuncturedLocalCuspQuotient A.starCuspWitness a)) =
      (Quotient.mk _ (A.cuspCoordinate.lift a.1.2) : A.FullBaseOrbitSpace) := by
  let _ := regularFamilyDeckAction A.periods
  rw [additiveCuspRadiusToPuncturedLocalCuspQuotient]
  rw [puncturedLocalCuspQuotientMap_mk]
  dsimp only [puncturedLocalCuspPrequotientMap, Function.comp_apply]
  rw [Homeomorph.symm_apply_apply, additiveCuspQuotientToGlobal_mk]
  rw [additiveCuspCoverToGlobal]
  change A.centralBaseOrbit (Quotient.mk _
    (regularCuspFamilyPoint A.cuspCoordinate a.1.2 _ a.1.1)) = _
  rw [A.centralBaseOrbit_mk]
  rfl

/-- Every central-family point has a neighborhood avoiding the sufficiently small cusp end. -/
public theorem exists_cuspCentralNeighborhood_avoids_small_collar
    (C : A.CentralFamily) :
    ∃ V : Set A.CentralFamily, IsOpen V ∧ C ∈ V ∧
      ∃ r : ℝ, 0 < r ∧ ∀ Q,
        puncturedLocalCuspRadius A.starCuspWitness Q < r →
          puncturedLocalCuspQuotientMap A.starCuspWitness Q ∉ V := by
  let Ubase := A.modular.modularParameter.toTriangleUniformization
  let hsource : Ubase.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := Ubase) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := triangleSourceMulAction Ubase
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    sourceActionProperlyDiscontinuous_to_instance hproper
  let _ : ContinuousConstSMul Delta UpperHalfPlane := ⟨fun g => by
    change Continuous (fun z : UpperHalfPlane => Ubase.sourceAction g • z)
    rw [hsource]
    exact (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let _ := regularFamilyDeckAction A.periods
  let q : UpperHalfPlane → A.FullBaseOrbitSpace := Quotient.mk _
  induction C using Quotient.inductionOn with
  | _ x =>
      let z₀ : UpperHalfPlane := (regularTotalSpaceBase A.periods x).1
      obtain ⟨S, hSopen, hzS, r, hr, hrle, havoid⟩ :=
        exists_sourceNeighborhood_avoids_deep_cusp_translates
          A.starCuspWitness z₀
      let T : Set A.FullBaseOrbitSpace := q '' S
      have hTopen : IsOpen T := isOpenMap_quotient_mk'_mul S hSopen
      let V : Set A.CentralFamily := A.centralBaseOrbit ⁻¹' T
      have hVopen : IsOpen V := hTopen.preimage A.centralBaseOrbit_continuous
      have hxV : (Quotient.mk _ x : A.CentralFamily) ∈ V := by
        change A.centralBaseOrbit (Quotient.mk _ x) ∈ T
        rw [A.centralBaseOrbit_mk]
        exact ⟨z₀, hzS, rfl⟩
      refine ⟨V, hVopen, hxV, r, hr, ?_⟩
      intro Q hsmall hmem
      obtain ⟨a, rfl⟩ :=
        additiveCuspRadiusToPuncturedLocalCuspQuotient_surjective
          A.starCuspWitness Q
      rw [A.puncturedLocalCuspRadius_additiveCuspRadiusToQuotient] at hsmall
      change A.centralBaseOrbit
        (puncturedLocalCuspQuotientMap A.starCuspWitness
          (additiveCuspRadiusToPuncturedLocalCuspQuotient
            A.starCuspWitness a)) ∈ T at hmem
      rw [A.centralBaseOrbit_puncturedCusp_additiveCuspRadiusToQuotient] at hmem
      obtain ⟨z, hzS', hzq⟩ := hmem
      have hrel := Quotient.exact hzq
      change MulAction.orbitRel Delta UpperHalfPlane z
        (A.cuspCoordinate.lift a.1.2) at hrel
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
      obtain ⟨g, hg⟩ := hrel
      apply havoid g a.1.2 hsmall
      change Ubase.sourceAction g • A.cuspCoordinate.lift a.1.2 = z at hg
      rw [hsource] at hg
      rw [hg]
      exact hzS'

/-- The actual cusp collar graph is closed.  Positive radius is controlled by its open
embedding, while the normalized modular height estimate separates the collapsed end. -/
public theorem cuspPuncturedCollarPairRange_isClosed :
    IsClosed (Set.range (fun Q : puncturedLocalCuspQuotient A.starCuspWitness =>
      (puncturedLocalCuspQuotientMap A.starCuspWitness Q,
        puncturedLocalCuspToFilling A.starCuspWitness Q))) := by
  let _ : T2Space A.CentralFamily := A.centralFamily_t2
  let _ : T2Space (actualLocalCuspFilling A.starCuspWitness) :=
    actualLocalCuspFilling_t2 A.starCuspWitness
  apply isClosed_range_prod_of_openEmbedding_radial_end
    (toCentral := puncturedLocalCuspQuotientMap A.starCuspWitness)
    (toFilling := puncturedLocalCuspToFilling A.starCuspWitness)
    (sourceRadius := puncturedLocalCuspRadius A.starCuspWitness)
    (fillingRadius := actualLocalCuspFillingRadius A.starCuspWitness)
  · exact (puncturedLocalCuspQuotientMap_isOpenEmbedding
      A.starCuspWitness).continuous
  · exact puncturedLocalCuspToFilling_isOpenEmbedding A.starCuspWitness
  · exact actualLocalCuspFillingRadius_continuous A.starCuspWitness
  · exact actualLocalCuspFillingRadius_nonneg A.starCuspWitness
  · exact actualLocalCuspFillingCollar_eq_positiveRadius A.starCuspWitness
  · exact actualLocalCuspFillingRadius_puncturedLocalCuspToFilling
      A.starCuspWitness
  · exact A.exists_cuspCentralNeighborhood_avoids_small_collar

/-- A canonical nonzero point of every sufficiently small elliptic disc. -/
@[expose] public noncomputable def puncturedEllipticDiscPoint
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : ComplexUnitDisc :=
  ⟨((r / 2 : ℝ) : ℂ), by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    exact (half_lt_self hr).trans hr1⟩

public theorem puncturedEllipticDiscPoint_norm_pos
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    0 < ‖(puncturedEllipticDiscPoint hr hr1 : ℂ)‖ := by
  rw [puncturedEllipticDiscPoint, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (half_pos hr)]
  exact half_pos hr

public theorem puncturedEllipticDiscPoint_norm_lt
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ‖(puncturedEllipticDiscPoint hr hr1 : ℂ)‖ < r := by
  rw [puncturedEllipticDiscPoint, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (half_pos hr)]
  exact half_lt_self hr

/-- The cusp filling followed by the order-three and order-four varying fillings. -/
@[expose] public noncomputable def starFillingType : Fin 3 → Type :=
  Fin.cases (actualLocalCuspFilling A.starCuspWitness) fun i ↦
    Fin.cases (A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius)
      (fun _ ↦ A.OrderFourVaryingFilling A.starSeparation.orderFour.radius) i

/-- The three common collar-source quotients. -/
@[expose] public noncomputable def starCollarSourceType : Fin 3 → Type :=
  Fin.cases (puncturedLocalCuspQuotient A.starCuspWitness) fun i ↦
    Fin.cases
      (Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderThree.radius)))
      (fun _ ↦ Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderFour.radius))) i

public noncomputable instance starFillingTopology (i : Fin 3) :
    TopologicalSpace (A.starFillingType i) := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change TopologicalSpace (actualLocalCuspFilling A.starCuspWitness)
    infer_instance
  · refine Fin.cases ?_ (fun _ ↦ ?_) j
    · change TopologicalSpace
        (A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius)
      infer_instance
    · change TopologicalSpace
        (A.OrderFourVaryingFilling A.starSeparation.orderFour.radius)
      infer_instance

public noncomputable instance starCollarSourceTopology (i : Fin 3) :
    TopologicalSpace (A.starCollarSourceType i) := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change TopologicalSpace (puncturedLocalCuspQuotient A.starCuspWitness)
    infer_instance
  · refine Fin.cases ?_ (fun _ ↦ ?_) j
    · change TopologicalSpace (Quotient (restrictedOrbitRel
        (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderThree.radius)))
      infer_instance
    · change TopologicalSpace (Quotient (restrictedOrbitRel
        (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderFour.radius)))
      infer_instance

/-- The three collar maps into the punctured global family. -/
@[expose] public noncomputable def starToCentral :
    ∀ i, A.starCollarSourceType i → A.CentralFamily :=
  Fin.cases (puncturedLocalCuspQuotientMap A.starCuspWitness) fun i ↦
    Fin.cases
      (A.orderThreePuncturedCollarToCentralFamily
        A.starSeparation.orderThree.sourceData)
      (fun _ ↦ A.orderFourPuncturedCollarToCentralFamily
        A.starSeparation.orderFour.sourceData) i

/-- The three collar maps into their filling pieces. -/
@[expose] public noncomputable def starToFilling :
    ∀ i, A.starCollarSourceType i → A.starFillingType i :=
  Fin.cases (puncturedLocalCuspToFilling A.starCuspWitness) fun i ↦
    Fin.cases
      (A.orderThreePuncturedCollarToFilling A.starSeparation.orderThree.radius)
      (fun _ ↦ A.orderFourPuncturedCollarToFilling A.starSeparation.orderFour.radius) i

/-- The closed half-radius core of the actual cusp filling. -/
@[expose] public def cuspStarFillingCore :
    Set (actualLocalCuspFilling A.starCuspWitness) :=
  {Q | actualLocalCuspFillingRadius A.starCuspWitness Q ≤
    A.starCuspWitness.localWitness.radius / 2}

/-- The closed half-radius core of the selected order-three filling. -/
@[expose] public def orderThreeStarFillingCore :
    Set (A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius) :=
  {Q | A.orderThreeFillingRadius A.starSeparation.orderThree.radius Q ≤
    A.starSeparation.orderThree.radius / 2}

/-- The closed half-radius core of the selected order-four filling. -/
@[expose] public def orderFourStarFillingCore :
    Set (A.OrderFourVaryingFilling A.starSeparation.orderFour.radius) :=
  {Q | A.orderFourFillingRadius A.starSeparation.orderFour.radius Q ≤
    A.starSeparation.orderFour.radius / 2}

/-- The three half-radius filling cores, indexed compatibly with the concrete star. -/
@[expose] public def starFillingCore : ∀ i, Set (A.starFillingType i) :=
  Fin.cases A.cuspStarFillingCore fun i ↦
    Fin.cases A.orderThreeStarFillingCore (fun _ ↦ A.orderFourStarFillingCore) i

/-- The cusp half-radius core is closed. -/
public theorem cuspStarFillingCore_isClosed : IsClosed A.cuspStarFillingCore := by
  exact isClosed_Iic.preimage
    (actualLocalCuspFillingRadius_continuous A.starCuspWitness)

/-- The actual cusp half-core is compact.  Uniform lattice reduction moves its noncentral
points into finitely many compact toric polydiscs, while the central fibre is represented by one
compact toric surface. -/
public theorem cuspStarFillingCore_isCompact : IsCompact A.cuspStarFillingCore := by
  change IsCompact
    (actualLocalCuspFillingRadius A.starCuspWitness ⁻¹'
      Set.Iic (A.starCuspWitness.localWitness.radius / 2))
  exact actualLocalCuspFilling_sublevel_isCompact A.starCuspWitness
    (le_of_lt (half_pos A.starCuspWitness.localWitness.radius_pos))
    (half_lt_self A.starCuspWitness.localWitness.radius_pos)

/-- The selected order-three half-radius core is compact. -/
public theorem orderThreeStarFillingCore_isCompact :
    IsCompact A.orderThreeStarFillingCore := by
  exact A.orderThreeFillingRadius_le_isCompact
    (half_lt_self A.starSeparation.orderThree.radius_pos)
    A.starSeparation.orderThree.radius_lt_one

/-- The selected order-four half-radius core is compact. -/
public theorem orderFourStarFillingCore_isCompact :
    IsCompact A.orderFourStarFillingCore := by
  exact A.orderFourFillingRadius_le_isCompact
    (half_lt_self A.starSeparation.orderFour.radius_pos)
    A.starSeparation.orderFour.radius_lt_one

/-- Every cusp-filling point lies in the half-radius core or in the punctured attaching
collar. -/
public theorem cuspStarFilling_mem_core_or_range (Q : actualLocalCuspFilling A.starCuspWitness) :
    Q ∈ A.cuspStarFillingCore ∨
      Q ∈ Set.range (puncturedLocalCuspToFilling A.starCuspWitness) := by
  by_cases hcore : Q ∈ A.cuspStarFillingCore
  · exact Or.inl hcore
  · right
    change Q ∈ actualLocalCuspFillingCollar A.starCuspWitness
    rw [actualLocalCuspFillingCollar_eq_positiveRadius]
    have hhalf : A.starCuspWitness.localWitness.radius / 2 <
        actualLocalCuspFillingRadius A.starCuspWitness Q :=
      lt_of_not_ge hcore
    exact (half_pos A.starCuspWitness.localWitness.radius_pos).trans hhalf

/-- Every order-three filling point lies in the compact half-radius core or in its punctured
attaching collar. -/
public theorem orderThreeStarFilling_mem_core_or_range
    (Q : A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius) :
    Q ∈ A.orderThreeStarFillingCore ∨
      Q ∈ Set.range (A.orderThreePuncturedCollarToFilling
        A.starSeparation.orderThree.radius) := by
  by_cases hcore : Q ∈ A.orderThreeStarFillingCore
  · exact Or.inl hcore
  · right
    rw [A.orderThreePuncturedCollarToFilling_range]
    have hhalf : A.starSeparation.orderThree.radius / 2 <
        A.orderThreeFillingRadius A.starSeparation.orderThree.radius Q :=
      lt_of_not_ge hcore
    exact (half_pos A.starSeparation.orderThree.radius_pos).trans hhalf

/-- Every order-four filling point lies in the compact half-radius core or in its punctured
attaching collar. -/
public theorem orderFourStarFilling_mem_core_or_range
    (Q : A.OrderFourVaryingFilling A.starSeparation.orderFour.radius) :
    Q ∈ A.orderFourStarFillingCore ∨
      Q ∈ Set.range (A.orderFourPuncturedCollarToFilling
        A.starSeparation.orderFour.radius) := by
  by_cases hcore : Q ∈ A.orderFourStarFillingCore
  · exact Or.inl hcore
  · right
    rw [A.orderFourPuncturedCollarToFilling_range]
    have hhalf : A.starSeparation.orderFour.radius / 2 <
        A.orderFourFillingRadius A.starSeparation.orderFour.radius Q :=
      lt_of_not_ge hcore
    exact (half_pos A.starSeparation.orderFour.radius_pos).trans hhalf

/-- Uniformly, every filling point is either in its half-radius core or comes from its common
collar source. -/
public theorem starFilling_mem_core_or_range (i : Fin 3) (Q : A.starFillingType i) :
    Q ∈ A.starFillingCore i ∨ Q ∈ Set.range (A.starToFilling i) := by
  fin_cases i
  · exact A.cuspStarFilling_mem_core_or_range Q
  · exact A.orderThreeStarFilling_mem_core_or_range Q
  · exact A.orderFourStarFilling_mem_core_or_range Q

public theorem starToCentral_isOpenEmbedding (i : Fin 3) :
    IsOpenEmbedding (A.starToCentral i) := by
  fin_cases i
  · exact puncturedLocalCuspQuotientMap_isOpenEmbedding A.starCuspWitness
  · exact A.orderThreePuncturedCollarToCentralFamily_isOpenEmbedding
      A.starSeparation.orderThree.sourceData
  · exact A.orderFourPuncturedCollarToCentralFamily_isOpenEmbedding
      A.starSeparation.orderFour.sourceData

public theorem starToFilling_isOpenEmbedding (i : Fin 3) :
    IsOpenEmbedding (A.starToFilling i) := by
  fin_cases i
  · exact puncturedLocalCuspToFilling_isOpenEmbedding A.starCuspWitness
  · exact A.orderThreePuncturedCollarToFilling_isOpenEmbedding
      A.starSeparation.orderThree.radius
  · exact A.orderFourPuncturedCollarToFilling_isOpenEmbedding
      A.starSeparation.orderFour.radius

public theorem starToCentral_ranges_pairwise : Pairwise fun i j ↦
    Disjoint (Set.range (A.starToCentral i)) (Set.range (A.starToCentral j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · simp at hij
  · exact A.starSeparation.cusp_orderThree_centralRanges_disjoint
  · exact A.starSeparation.cusp_orderFour_centralRanges_disjoint
  · exact A.starSeparation.cusp_orderThree_centralRanges_disjoint.symm
  · simp at hij
  · exact A.starSeparation.elliptic_centralRanges_disjoint
  · exact A.starSeparation.cusp_orderFour_centralRanges_disjoint.symm
  · exact A.starSeparation.elliptic_centralRanges_disjoint.symm
  · simp at hij

/-- Each of the three concrete common collar sources contains an explicit orbit class. -/
public theorem starCollarSource_nonempty (i : Fin 3) :
    Nonempty (A.starCollarSourceType i) := by
  fin_cases i
  · change Nonempty (puncturedLocalCuspQuotient A.starCuspWitness)
    exact ⟨Quotient.mk _ (puncturedLocalCarrier_nonempty A.starCuspWitness).some⟩
  · let P := A.starSeparation.orderThree
    let w : ComplexUnitDisc :=
      puncturedEllipticDiscPoint P.radius_pos P.radius_lt_one
    let q : TotalSpace (parameterMap A.periods) :=
      Quotient.mk _ (orderThreeCayleyHomeomorph.symm w, 0)
    have hq : q ∈ orderThreePuncturedFamilyCollar A.periods P.radius := by
      change 0 < orderThreeFamilyRadius A.periods q ∧
        orderThreeFamilyRadius A.periods q < P.radius
      simpa only [q, w, orderThreeFamilyRadius, familyTotalSpaceBase_mk,
        orderThreeCayleyHomeomorph.apply_symm_apply] using
          ⟨puncturedEllipticDiscPoint_norm_pos P.radius_pos P.radius_lt_one,
            puncturedEllipticDiscPoint_norm_lt P.radius_pos P.radius_lt_one⟩
    change Nonempty (Quotient (restrictedOrbitRel
      (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction P.radius)))
    exact ⟨Quotient.mk _ ⟨q, hq⟩⟩
  · let P := A.starSeparation.orderFour
    let w : ComplexUnitDisc :=
      puncturedEllipticDiscPoint P.radius_pos P.radius_lt_one
    let q : TotalSpace (parameterMap A.periods) :=
      Quotient.mk _ (orderFourCayleyHomeomorph.symm w, 0)
    have hq : q ∈ orderFourPuncturedFamilyCollar A.periods P.radius := by
      change 0 < orderFourFamilyRadius A.periods q ∧
        orderFourFamilyRadius A.periods q < P.radius
      simpa only [q, w, orderFourFamilyRadius, familyTotalSpaceBase_mk,
        orderFourCayleyHomeomorph.apply_symm_apply] using
          ⟨puncturedEllipticDiscPoint_norm_pos P.radius_pos P.radius_lt_one,
            puncturedEllipticDiscPoint_norm_lt P.radius_pos P.radius_lt_one⟩
    change Nonempty (Quotient (restrictedOrbitRel
      (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction P.radius)))
    exact ⟨Quotient.mk _ ⟨q, hq⟩⟩

/-- Each of the three concrete common collar sources is path connected. -/
public theorem starCollarSource_pathConnected (i : Fin 3) :
    PathConnectedSpace (A.starCollarSourceType i) := by
  fin_cases i
  · change PathConnectedSpace (puncturedLocalCuspQuotient A.starCuspWitness)
    let _ := puncturedLocalCuspQuotientCharts A.starCuspWitness
    let _ : ConnectedSpace (puncturedLocalCuspQuotient A.starCuspWitness) :=
      puncturedLocalCuspQuotient_connected A.starCuspWitness
    let _ : LocallyPathConnectedSpace
        (puncturedLocalCuspQuotient A.starCuspWitness) :=
      ChartedSpace.locallyPathConnectedSpace ComplexModel
        (puncturedLocalCuspQuotient A.starCuspWitness)
    exact PathConnectedSpace.of_locallyPathConnectedSpace
  · let P := A.starSeparation.orderThree
    change PathConnectedSpace (Quotient (restrictedOrbitRel
      (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction P.radius)))
    let _ : PathConnectedSpace ((orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        P.radius).carrier) :=
      A.orderThreeAffinePuncturedCarrier_pathConnected P.radius_pos P.radius_lt_one
    infer_instance
  · let P := A.starSeparation.orderFour
    change PathConnectedSpace (Quotient (restrictedOrbitRel
      (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction P.radius)))
    let _ : PathConnectedSpace ((orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction
        P.radius).carrier) :=
      A.orderFourAffinePuncturedCarrier_pathConnected P.radius_pos P.radius_lt_one
    infer_instance

/-- The three concrete filling pieces are second countable. -/
public theorem starFilling_secondCountable (i : Fin 3) :
    SecondCountableTopology (A.starFillingType i) := by
  fin_cases i
  · let W := A.starCuspWitness
    let C :=
      CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
        A.cuspCoordinate A.toricModel W.localWitness.radius W.localWitness.radius_pos
          W.localWitness.radius_le
    let _ : MulAction (Multiplicative ParameterLattice)
        (LocalCarrier A.toricModel W.localWitness.radius) :=
      (C.toCuspActionData W.localWitness.fixedPoint).psiAction
    let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
        (LocalCarrier A.toricModel W.localWitness.radius) := ⟨by
      intro lambda
      rw [show lambda = Multiplicative.ofAdd (Multiplicative.toAdd lambda) from rfl]
      change Continuous ((C.toCuspActionData W.localWitness.fixedPoint).psiMap
        (Multiplicative.toAdd lambda))
      exact (C.genericPsiMap_holomorphic W.localWitness.fixedPoint _).continuous⟩
    let _ : SecondCountableTopology
        (LocalCarrier A.toricModel W.localWitness.radius) := by infer_instance
    change SecondCountableTopology (Quotient
      (MulAction.orbitRel (Multiplicative ParameterLattice)
        (LocalCarrier A.toricModel W.localWitness.radius)))
    exact ContinuousConstSMul.secondCountableTopology
  · exact A.orderThreeFilling_secondCountable A.starSeparation.orderThree.radius
  · exact A.orderFourFilling_secondCountable A.starSeparation.orderFour.radius

/-- The three concrete filling pieces are connected. -/
public theorem starFilling_connected (i : Fin 3) :
    ConnectedSpace (A.starFillingType i) := by
  fin_cases i
  · exact actualLocalCuspFilling_connected A.starCuspWitness
  · exact A.orderThreeFilling_connected A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one
  · exact A.orderFourFilling_connected A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one

/-- All three selected filling pieces are Hausdorff. -/
public theorem starFilling_t2 (i : Fin 3) :
    T2Space (A.starFillingType i) := by
  fin_cases i
  · exact actualLocalCuspFilling_t2 A.starCuspWitness
  · exact A.orderThreeFilling_t2 A.starSeparation.orderThree.radius
  · exact A.orderFourFilling_t2 A.starSeparation.orderFour.radius

/-- Complex threefold charts on each of the three concrete filling pieces. -/
@[expose, instance_reducible] public noncomputable def starFillingComplexCharts :
    ∀ i, ChartedSpace ComplexModel (A.starFillingType i) :=
  Fin.cases (actualLocalCuspFillingCharts A.starCuspWitness) fun i ↦
    Fin.cases
      (A.orderThreeFillingComplexCharts A.starSeparation.orderThree.radius)
      (fun _ ↦ A.orderFourFillingComplexCharts A.starSeparation.orderFour.radius) i

/-- Each selected cusp or elliptic filling is a complex three-manifold. -/
public theorem starFilling_isManifold :
    letI (i : Fin 3) := A.starFillingComplexCharts i
    ∀ i : Fin 3, IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.starFillingType i) := by
  let _ (i : Fin 3) := A.starFillingComplexCharts i
  intro i
  fin_cases i
  · exact actualLocalCuspFilling_isManifold A.starCuspWitness
  · exact A.orderThreeFilling_isManifold A.starSeparation.orderThree.radius
  · exact A.orderFourFilling_isManifold A.starSeparation.orderFour.radius

/-- The actual cusp and elliptic collars, as a concrete common-source star. -/
@[expose] public noncomputable def openEmbeddingStarData :
    SphereSixComplex.OpenEmbeddingStarData where
  central := TopCat.of A.CentralFamily
  filling i := TopCat.of (A.starFillingType i)
  collarSource i := TopCat.of (A.starCollarSourceType i)
  toCentral i := TopCat.ofHom ⟨A.starToCentral i,
    (A.starToCentral_isOpenEmbedding i).continuous⟩
  toFilling i := TopCat.ofHom ⟨A.starToFilling i,
    (A.starToFilling_isOpenEmbedding i).continuous⟩
  toCentral_isOpenEmbedding := A.starToCentral_isOpenEmbedding
  toFilling_isOpenEmbedding := A.starToFilling_isOpenEmbedding
  centralRange_disjoint := A.starToCentral_ranges_pairwise

@[expose, instance_reducible]
public noncomputable def cuspStarCollarComplexCharts :
    ChartedSpace ComplexModel (A.starCollarSourceType 0) :=
  puncturedLocalCuspQuotientCharts A.starCuspWitness

@[expose, instance_reducible]
public noncomputable def orderThreeStarCollarComplexCharts :
    ChartedSpace ComplexModel (A.starCollarSourceType 1) :=
  A.orderThreePuncturedCollarComplexCharts A.starSeparation.orderThree.radius

@[expose, instance_reducible]
public noncomputable def orderFourStarCollarComplexCharts :
    ChartedSpace ComplexModel (A.starCollarSourceType 2) :=
  A.orderFourPuncturedCollarComplexCharts A.starSeparation.orderFour.radius

/-- With the collar atlas transported from the actual toric filling, the cusp arm of the
common-source star is locally biholomorphic on its filling side. -/
public theorem cuspStarToFilling_isLocalDiffeomorph_complex :
    letI := A.cuspStarCollarComplexCharts
    letI := A.starFillingComplexCharts 0
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.starToFilling 0) := by
  let _ := A.cuspStarCollarComplexCharts
  let _ := A.starFillingComplexCharts 0
  letI : ChartedSpace ComplexModel
      (puncturedLocalCuspQuotient A.starCuspWitness) :=
    puncturedLocalCuspQuotientCharts A.starCuspWitness
  letI : ChartedSpace ComplexModel
      (actualLocalCuspFilling A.starCuspWitness) :=
    actualLocalCuspFillingCharts A.starCuspWitness
  change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
    (modelWithCornersSelf ℂ ComplexModel) ∞
    (puncturedLocalCuspToFilling A.starCuspWitness)
  exact puncturedLocalCuspToFilling_isLocalDiffeomorph A.starCuspWitness

/-- The cusp collar map into the punctured global family is locally biholomorphic in the
canonical `ℂ³` atlases used by the four-piece gluing. -/
public theorem cuspStarToCentral_isLocalDiffeomorph_complex :
    letI := A.cuspStarCollarComplexCharts
    letI := A.centralFamilyComplexCharts
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.starToCentral 0) := by
  let _ := A.cuspStarCollarComplexCharts
  let _ := A.centralFamilyProductCharts
  let _ := A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel
      (puncturedLocalCuspQuotient A.starCuspWitness) :=
    puncturedLocalCuspQuotientCharts A.starCuspWitness
  have hproduct : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      GlobalDeckTotalModel ∞
      (puncturedLocalCuspQuotientMap A.starCuspWitness) := by
    simpa only [RegularSmoothnessOrder] using
      puncturedLocalCuspQuotientMap_isLocalDiffeomorph A.starCuspWitness
  change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
    (modelWithCornersSelf ℂ ComplexModel) ∞
    (puncturedLocalCuspQuotientMap A.starCuspWitness)
  exact globalDeckComplexLocalDiffeomorph_target hproduct

public theorem orderThreeStarToCentral_isLocalDiffeomorph_complex :
    letI := A.orderThreeStarCollarComplexCharts
    letI := A.centralFamilyComplexCharts
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.starToCentral 1) := by
  let _ := A.orderThreeStarCollarComplexCharts
  let _ := A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel
      (Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderThree.radius))) :=
    A.orderThreePuncturedCollarComplexCharts A.starSeparation.orderThree.radius
  change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
    (modelWithCornersSelf ℂ ComplexModel) ∞
    (A.orderThreePuncturedCollarToCentralFamily
      A.starSeparation.orderThree.sourceData)
  exact A.orderThreePuncturedCollarToCentralFamily_isLocalDiffeomorph_complex
    A.starSeparation.orderThree.sourceData

public theorem orderThreeStarToFilling_isLocalDiffeomorph_complex :
    letI := A.orderThreeStarCollarComplexCharts
    letI := A.starFillingComplexCharts 1
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.starToFilling 1) := by
  let _ := A.orderThreeStarCollarComplexCharts
  let _ := A.starFillingComplexCharts 1
  letI : ChartedSpace ComplexModel
      (Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderThree.radius))) :=
    A.orderThreePuncturedCollarComplexCharts A.starSeparation.orderThree.radius
  letI : ChartedSpace ComplexModel
      (A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius) :=
    A.orderThreeFillingComplexCharts A.starSeparation.orderThree.radius
  change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
    (modelWithCornersSelf ℂ ComplexModel) ∞
    (A.orderThreePuncturedCollarToFilling A.starSeparation.orderThree.radius)
  exact A.orderThreePuncturedCollarToFilling_isLocalDiffeomorph_complex
    A.starSeparation.orderThree.radius

public theorem orderFourStarToCentral_isLocalDiffeomorph_complex :
    letI := A.orderFourStarCollarComplexCharts
    letI := A.centralFamilyComplexCharts
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.starToCentral 2) := by
  let _ := A.orderFourStarCollarComplexCharts
  let _ := A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel
      (Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderFour.radius))) :=
    A.orderFourPuncturedCollarComplexCharts A.starSeparation.orderFour.radius
  change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
    (modelWithCornersSelf ℂ ComplexModel) ∞
    (A.orderFourPuncturedCollarToCentralFamily
      A.starSeparation.orderFour.sourceData)
  exact A.orderFourPuncturedCollarToCentralFamily_isLocalDiffeomorph_complex
    A.starSeparation.orderFour.sourceData

public theorem orderFourStarToFilling_isLocalDiffeomorph_complex :
    letI := A.orderFourStarCollarComplexCharts
    letI := A.starFillingComplexCharts 2
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.starToFilling 2) := by
  let _ := A.orderFourStarCollarComplexCharts
  let _ := A.starFillingComplexCharts 2
  letI : ChartedSpace ComplexModel
      (Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderFour.radius))) :=
    A.orderFourPuncturedCollarComplexCharts A.starSeparation.orderFour.radius
  letI : ChartedSpace ComplexModel
      (A.OrderFourVaryingFilling A.starSeparation.orderFour.radius) :=
    A.orderFourFillingComplexCharts A.starSeparation.orderFour.radius
  change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
    (modelWithCornersSelf ℂ ComplexModel) ∞
    (A.orderFourPuncturedCollarToFilling A.starSeparation.orderFour.radius)
  exact A.orderFourPuncturedCollarToFilling_isLocalDiffeomorph_complex
    A.starSeparation.orderFour.radius

/-- The actual cusp attaching map, packaged as an ambient biholomorphic partial map between
its central and toric-filling collar images. -/
@[expose] public noncomputable def cuspStarCollarPartialDiffeomorph :
    letI := A.centralFamilyComplexCharts
    letI := A.starFillingComplexCharts 0
    PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) A.CentralFamily
      (A.starFillingType 0) ∞ := by
  letI : ChartedSpace ComplexModel A.CentralFamily := A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel (A.starFillingType 0) :=
    A.starFillingComplexCharts 0
  letI collarCharts : ChartedSpace ComplexModel
      (puncturedLocalCuspQuotient A.starCuspWitness) :=
    puncturedLocalCuspQuotientCharts A.starCuspWitness
  letI : ChartedSpace ComplexModel (A.starCollarSourceType 0) := collarCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.collarSource 0) :=
    collarCharts
  letI : ChartedSpace ComplexModel ↑A.openEmbeddingStarData.central :=
    A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.filling 0) :=
    A.starFillingComplexCharts 0
  letI : Nonempty (A.starCollarSourceType 0) := A.starCollarSource_nonempty 0
  letI : Nonempty ↑(A.openEmbeddingStarData.collarSource 0) := by
    change Nonempty (A.starCollarSourceType 0)
    infer_instance
  have hcentral : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.starToCentral 0) :=
    A.cuspStarToCentral_isLocalDiffeomorph_complex
  have hfilling : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.starToFilling 0) :=
    A.cuspStarToFilling_isLocalDiffeomorph_complex
  exact A.openEmbeddingStarData.collarPartialDiffeomorphOfLocalDiffeomorph
    0 hcentral hfilling

@[simp]
public theorem cuspStarCollarPartialDiffeomorph_source :
    letI := A.centralFamilyComplexCharts
    letI := A.starFillingComplexCharts 0
    A.cuspStarCollarPartialDiffeomorph.source =
      Set.range (A.starToCentral 0) := by
  let _ := A.centralFamilyComplexCharts
  let _ := A.starFillingComplexCharts 0
  letI : ChartedSpace ComplexModel (A.starCollarSourceType 0) :=
    A.cuspStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.collarSource 0) :=
    A.cuspStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑A.openEmbeddingStarData.central :=
    A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.filling 0) :=
    A.starFillingComplexCharts 0
  letI : Nonempty (A.starCollarSourceType 0) := A.starCollarSource_nonempty 0
  letI : Nonempty ↑(A.openEmbeddingStarData.collarSource 0) :=
    A.starCollarSource_nonempty 0
  have hcentral := A.cuspStarToCentral_isLocalDiffeomorph_complex
  have hfilling := A.cuspStarToFilling_isLocalDiffeomorph_complex
  rw [cuspStarCollarPartialDiffeomorph.eq_def]
  have h := A.openEmbeddingStarData.collarPartialDiffeomorphOfLocalDiffeomorph_source
    0 hcentral hfilling
  change _ = Set.range (A.starToCentral 0) at h
  exact h

@[simp]
public theorem cuspStarCollarPartialDiffeomorph_target :
    letI := A.centralFamilyComplexCharts
    letI := A.starFillingComplexCharts 0
    A.cuspStarCollarPartialDiffeomorph.target =
      Set.range (A.starToFilling 0) := by
  let _ := A.centralFamilyComplexCharts
  let _ := A.starFillingComplexCharts 0
  letI : ChartedSpace ComplexModel (A.starCollarSourceType 0) :=
    A.cuspStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.collarSource 0) :=
    A.cuspStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑A.openEmbeddingStarData.central :=
    A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.filling 0) :=
    A.starFillingComplexCharts 0
  letI : Nonempty (A.starCollarSourceType 0) := A.starCollarSource_nonempty 0
  letI : Nonempty ↑(A.openEmbeddingStarData.collarSource 0) :=
    A.starCollarSource_nonempty 0
  have hcentral := A.cuspStarToCentral_isLocalDiffeomorph_complex
  have hfilling := A.cuspStarToFilling_isLocalDiffeomorph_complex
  rw [cuspStarCollarPartialDiffeomorph.eq_def]
  have h := A.openEmbeddingStarData.collarPartialDiffeomorphOfLocalDiffeomorph_target
    0 hcentral hfilling
  change _ = Set.range (A.starToFilling 0) at h
  exact h

@[simp]
public theorem cuspStarCollarPartialDiffeomorph_toCentral
    (x : A.starCollarSourceType 0) :
    letI := A.centralFamilyComplexCharts
    letI := A.starFillingComplexCharts 0
    A.cuspStarCollarPartialDiffeomorph (A.starToCentral 0 x) =
      A.starToFilling 0 x := by
  let _ := A.centralFamilyComplexCharts
  let _ := A.starFillingComplexCharts 0
  letI : ChartedSpace ComplexModel (A.starCollarSourceType 0) :=
    A.cuspStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.collarSource 0) :=
    A.cuspStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑A.openEmbeddingStarData.central :=
    A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.filling 0) :=
    A.starFillingComplexCharts 0
  letI : Nonempty (A.starCollarSourceType 0) := A.starCollarSource_nonempty 0
  letI : Nonempty ↑(A.openEmbeddingStarData.collarSource 0) :=
    A.starCollarSource_nonempty 0
  have hcentral := A.cuspStarToCentral_isLocalDiffeomorph_complex
  have hfilling := A.cuspStarToFilling_isLocalDiffeomorph_complex
  rw [cuspStarCollarPartialDiffeomorph.eq_def]
  exact A.openEmbeddingStarData.collarPartialDiffeomorphOfLocalDiffeomorph_toCentral
    0 hcentral hfilling x

/-- The actual order-three attaching map, packaged as an ambient biholomorphic partial map
between its central and filling collar images. -/
@[expose] public noncomputable def orderThreeStarCollarPartialDiffeomorph :
    letI := A.centralFamilyComplexCharts
    letI := A.starFillingComplexCharts 1
    PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) A.CentralFamily
      (A.starFillingType 1) ∞ := by
  letI : ChartedSpace ComplexModel A.CentralFamily := A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel (A.starFillingType 1) :=
    A.starFillingComplexCharts 1
  letI : ChartedSpace ComplexModel
      (A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius) :=
    A.starFillingComplexCharts 1
  letI collarCharts : ChartedSpace ComplexModel
      (Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderThree.radius))) :=
    A.orderThreePuncturedCollarComplexCharts A.starSeparation.orderThree.radius
  letI : ChartedSpace ComplexModel (A.starCollarSourceType 1) := collarCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.collarSource 1) :=
    collarCharts
  letI : ChartedSpace ComplexModel ↑A.openEmbeddingStarData.central :=
    A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.filling 1) :=
    A.starFillingComplexCharts 1
  letI : Nonempty (A.starCollarSourceType 1) := A.starCollarSource_nonempty 1
  letI : Nonempty ↑(A.openEmbeddingStarData.collarSource 1) := by
    change Nonempty (A.starCollarSourceType 1)
    infer_instance
  have hcentral : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.starToCentral 1) := by
    change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.orderThreePuncturedCollarToCentralFamily
        A.starSeparation.orderThree.sourceData)
    exact A.orderThreePuncturedCollarToCentralFamily_isLocalDiffeomorph_complex
      A.starSeparation.orderThree.sourceData
  have hfilling : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.starToFilling 1) := by
    change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.orderThreePuncturedCollarToFilling A.starSeparation.orderThree.radius)
    exact A.orderThreePuncturedCollarToFilling_isLocalDiffeomorph_complex
      A.starSeparation.orderThree.radius
  exact A.openEmbeddingStarData.collarPartialDiffeomorphOfLocalDiffeomorph
    1 hcentral hfilling

/-- The actual order-four attaching map, packaged as an ambient biholomorphic partial map
between its central and filling collar images. -/
@[expose] public noncomputable def orderFourStarCollarPartialDiffeomorph :
    letI := A.centralFamilyComplexCharts
    letI := A.starFillingComplexCharts 2
    PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) A.CentralFamily
      (A.starFillingType 2) ∞ := by
  letI : ChartedSpace ComplexModel A.CentralFamily := A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel (A.starFillingType 2) :=
    A.starFillingComplexCharts 2
  letI : ChartedSpace ComplexModel
      (A.OrderFourVaryingFilling A.starSeparation.orderFour.radius) :=
    A.starFillingComplexCharts 2
  letI collarCharts : ChartedSpace ComplexModel
      (Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction
          A.starSeparation.orderFour.radius))) :=
    A.orderFourPuncturedCollarComplexCharts A.starSeparation.orderFour.radius
  letI : ChartedSpace ComplexModel (A.starCollarSourceType 2) := collarCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.collarSource 2) :=
    collarCharts
  letI : ChartedSpace ComplexModel ↑A.openEmbeddingStarData.central :=
    A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.filling 2) :=
    A.starFillingComplexCharts 2
  letI : Nonempty (A.starCollarSourceType 2) := A.starCollarSource_nonempty 2
  letI : Nonempty ↑(A.openEmbeddingStarData.collarSource 2) := by
    change Nonempty (A.starCollarSourceType 2)
    infer_instance
  have hcentral : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.starToCentral 2) := by
    change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.orderFourPuncturedCollarToCentralFamily
        A.starSeparation.orderFour.sourceData)
    exact A.orderFourPuncturedCollarToCentralFamily_isLocalDiffeomorph_complex
      A.starSeparation.orderFour.sourceData
  have hfilling : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (A.starToFilling 2) := by
    change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.orderFourPuncturedCollarToFilling A.starSeparation.orderFour.radius)
    exact A.orderFourPuncturedCollarToFilling_isLocalDiffeomorph_complex
      A.starSeparation.orderFour.radius
  exact A.openEmbeddingStarData.collarPartialDiffeomorphOfLocalDiffeomorph
    2 hcentral hfilling

@[simp]
public theorem orderThreeStarCollarPartialDiffeomorph_source :
    letI := A.centralFamilyComplexCharts
    letI := A.starFillingComplexCharts 1
    A.orderThreeStarCollarPartialDiffeomorph.source =
      Set.range (A.starToCentral 1) := by
  let _ := A.centralFamilyComplexCharts
  let _ := A.starFillingComplexCharts 1
  letI : ChartedSpace ComplexModel (A.starCollarSourceType 1) :=
    A.orderThreeStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.collarSource 1) :=
    A.orderThreeStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑A.openEmbeddingStarData.central :=
    A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.filling 1) :=
    A.starFillingComplexCharts 1
  letI : Nonempty (A.starCollarSourceType 1) := A.starCollarSource_nonempty 1
  letI : Nonempty ↑(A.openEmbeddingStarData.collarSource 1) :=
    A.starCollarSource_nonempty 1
  have hcentral := A.orderThreeStarToCentral_isLocalDiffeomorph_complex
  have hfilling := A.orderThreeStarToFilling_isLocalDiffeomorph_complex
  rw [orderThreeStarCollarPartialDiffeomorph.eq_def]
  have h := A.openEmbeddingStarData.collarPartialDiffeomorphOfLocalDiffeomorph_source
    1 hcentral hfilling
  change _ = Set.range (A.starToCentral 1) at h
  exact h

@[simp]
public theorem orderThreeStarCollarPartialDiffeomorph_target :
    letI := A.centralFamilyComplexCharts
    letI := A.starFillingComplexCharts 1
    A.orderThreeStarCollarPartialDiffeomorph.target =
      Set.range (A.starToFilling 1) := by
  let _ := A.centralFamilyComplexCharts
  let _ := A.starFillingComplexCharts 1
  letI : ChartedSpace ComplexModel (A.starCollarSourceType 1) :=
    A.orderThreeStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.collarSource 1) :=
    A.orderThreeStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑A.openEmbeddingStarData.central :=
    A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.filling 1) :=
    A.starFillingComplexCharts 1
  letI : Nonempty (A.starCollarSourceType 1) := A.starCollarSource_nonempty 1
  letI : Nonempty ↑(A.openEmbeddingStarData.collarSource 1) :=
    A.starCollarSource_nonempty 1
  have hcentral := A.orderThreeStarToCentral_isLocalDiffeomorph_complex
  have hfilling := A.orderThreeStarToFilling_isLocalDiffeomorph_complex
  rw [orderThreeStarCollarPartialDiffeomorph.eq_def]
  have h := A.openEmbeddingStarData.collarPartialDiffeomorphOfLocalDiffeomorph_target
    1 hcentral hfilling
  change _ = Set.range (A.starToFilling 1) at h
  exact h

@[simp]
public theorem orderThreeStarCollarPartialDiffeomorph_toCentral
    (x : A.starCollarSourceType 1) :
    letI := A.centralFamilyComplexCharts
    letI := A.starFillingComplexCharts 1
    A.orderThreeStarCollarPartialDiffeomorph (A.starToCentral 1 x) =
      A.starToFilling 1 x := by
  let _ := A.centralFamilyComplexCharts
  let _ := A.starFillingComplexCharts 1
  letI : ChartedSpace ComplexModel (A.starCollarSourceType 1) :=
    A.orderThreeStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.collarSource 1) :=
    A.orderThreeStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑A.openEmbeddingStarData.central :=
    A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.filling 1) :=
    A.starFillingComplexCharts 1
  letI : Nonempty (A.starCollarSourceType 1) := A.starCollarSource_nonempty 1
  letI : Nonempty ↑(A.openEmbeddingStarData.collarSource 1) :=
    A.starCollarSource_nonempty 1
  have hcentral := A.orderThreeStarToCentral_isLocalDiffeomorph_complex
  have hfilling := A.orderThreeStarToFilling_isLocalDiffeomorph_complex
  rw [orderThreeStarCollarPartialDiffeomorph.eq_def]
  exact A.openEmbeddingStarData.collarPartialDiffeomorphOfLocalDiffeomorph_toCentral
    1 hcentral hfilling x

@[simp]
public theorem orderFourStarCollarPartialDiffeomorph_source :
    letI := A.centralFamilyComplexCharts
    letI := A.starFillingComplexCharts 2
    A.orderFourStarCollarPartialDiffeomorph.source =
      Set.range (A.starToCentral 2) := by
  let _ := A.centralFamilyComplexCharts
  let _ := A.starFillingComplexCharts 2
  letI : ChartedSpace ComplexModel (A.starCollarSourceType 2) :=
    A.orderFourStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.collarSource 2) :=
    A.orderFourStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑A.openEmbeddingStarData.central :=
    A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.filling 2) :=
    A.starFillingComplexCharts 2
  letI : Nonempty (A.starCollarSourceType 2) := A.starCollarSource_nonempty 2
  letI : Nonempty ↑(A.openEmbeddingStarData.collarSource 2) :=
    A.starCollarSource_nonempty 2
  have hcentral := A.orderFourStarToCentral_isLocalDiffeomorph_complex
  have hfilling := A.orderFourStarToFilling_isLocalDiffeomorph_complex
  rw [orderFourStarCollarPartialDiffeomorph.eq_def]
  have h := A.openEmbeddingStarData.collarPartialDiffeomorphOfLocalDiffeomorph_source
    2 hcentral hfilling
  change _ = Set.range (A.starToCentral 2) at h
  exact h

@[simp]
public theorem orderFourStarCollarPartialDiffeomorph_target :
    letI := A.centralFamilyComplexCharts
    letI := A.starFillingComplexCharts 2
    A.orderFourStarCollarPartialDiffeomorph.target =
      Set.range (A.starToFilling 2) := by
  let _ := A.centralFamilyComplexCharts
  let _ := A.starFillingComplexCharts 2
  letI : ChartedSpace ComplexModel (A.starCollarSourceType 2) :=
    A.orderFourStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.collarSource 2) :=
    A.orderFourStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑A.openEmbeddingStarData.central :=
    A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.filling 2) :=
    A.starFillingComplexCharts 2
  letI : Nonempty (A.starCollarSourceType 2) := A.starCollarSource_nonempty 2
  letI : Nonempty ↑(A.openEmbeddingStarData.collarSource 2) :=
    A.starCollarSource_nonempty 2
  have hcentral := A.orderFourStarToCentral_isLocalDiffeomorph_complex
  have hfilling := A.orderFourStarToFilling_isLocalDiffeomorph_complex
  rw [orderFourStarCollarPartialDiffeomorph.eq_def]
  have h := A.openEmbeddingStarData.collarPartialDiffeomorphOfLocalDiffeomorph_target
    2 hcentral hfilling
  change _ = Set.range (A.starToFilling 2) at h
  exact h

@[simp]
public theorem orderFourStarCollarPartialDiffeomorph_toCentral
    (x : A.starCollarSourceType 2) :
    letI := A.centralFamilyComplexCharts
    letI := A.starFillingComplexCharts 2
    A.orderFourStarCollarPartialDiffeomorph (A.starToCentral 2 x) =
      A.starToFilling 2 x := by
  let _ := A.centralFamilyComplexCharts
  let _ := A.starFillingComplexCharts 2
  letI : ChartedSpace ComplexModel (A.starCollarSourceType 2) :=
    A.orderFourStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.collarSource 2) :=
    A.orderFourStarCollarComplexCharts
  letI : ChartedSpace ComplexModel ↑A.openEmbeddingStarData.central :=
    A.centralFamilyComplexCharts
  letI : ChartedSpace ComplexModel ↑(A.openEmbeddingStarData.filling 2) :=
    A.starFillingComplexCharts 2
  letI : Nonempty (A.starCollarSourceType 2) := A.starCollarSource_nonempty 2
  letI : Nonempty ↑(A.openEmbeddingStarData.collarSource 2) :=
    A.starCollarSource_nonempty 2
  have hcentral := A.orderFourStarToCentral_isLocalDiffeomorph_complex
  have hfilling := A.orderFourStarToFilling_isLocalDiffeomorph_complex
  rw [orderFourStarCollarPartialDiffeomorph.eq_def]
  exact A.openEmbeddingStarData.collarPartialDiffeomorphOfLocalDiffeomorph_toCentral
    2 hcentral hfilling x

/-- The concrete complex structures and biholomorphic collar maps on the punctured family and
its three fillings. -/
@[expose] public noncomputable def openEmbeddingStarBiholomorphicData :
    A.openEmbeddingStarData.BiholomorphicData where
  centralCharts := A.centralFamilyComplexCharts
  fillingCharts := A.starFillingComplexCharts
  centralManifold := A.centralFamily_isManifold
  fillingManifold := A.starFilling_isManifold
  collar := Fin.cases A.cuspStarCollarPartialDiffeomorph fun i ↦
    Fin.cases A.orderThreeStarCollarPartialDiffeomorph
      (fun _ ↦ A.orderFourStarCollarPartialDiffeomorph) i
  collar_source i := by
    fin_cases i
    · exact A.cuspStarCollarPartialDiffeomorph_source
    · exact A.orderThreeStarCollarPartialDiffeomorph_source
    · exact A.orderFourStarCollarPartialDiffeomorph_source
  collar_target i := by
    fin_cases i
    · exact A.cuspStarCollarPartialDiffeomorph_target
    · exact A.orderThreeStarCollarPartialDiffeomorph_target
    · exact A.orderFourStarCollarPartialDiffeomorph_target
  collar_toCentral i x := by
    fin_cases i
    · exact A.cuspStarCollarPartialDiffeomorph_toCentral x
    · exact A.orderThreeStarCollarPartialDiffeomorph_toCentral x
    · exact A.orderFourStarCollarPartialDiffeomorph_toCentral x

/-- The actual four-piece star built from the punctured family and its three fillings. -/
@[expose] public noncomputable def fourPieceStarGluingData :
    SphereSixComplex.FourPieceStarGluingData :=
  A.openEmbeddingStarData.toFourPieceStarGluingData

/-- A sufficiently small normalized-coordinate neighborhood of zero is covered by the compact
half-core of the selected order-three filling. -/
public theorem exists_orderThreeStarCore_coordinate_cover :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : A.CentralFamily,
      dist (A.centralBaseCoordinate C) 0 < ε →
        ∃ Q : A.starFillingType 1, Q ∈ A.starFillingCore 1 ∧
          A.fourPieceStarGluingData.glueData.toGlueData.ι none C =
            A.fourPieceStarGluingData.glueData.toGlueData.ι (some 1) Q := by
  let P := A.starSeparation.orderThree
  obtain ⟨ε, hε, hcover⟩ :=
    A.exists_orderThree_fullBaseCoordinate_ball_cayley
      (P.radius / 2) (half_pos P.radius_pos)
  refine ⟨ε, hε, ?_⟩
  intro C hC
  change dist (A.fullBaseOrbitHomeomorphComplex (A.centralBaseOrbit C)) 0 < ε at hC
  obtain ⟨z, hz, hbase⟩ := hcover (A.centralBaseOrbit C) hC
  have hzOuter : ‖(orderThreeCayleyHomeomorph z).1‖ < P.radius :=
    hz.trans (half_lt_self P.radius_pos)
  obtain ⟨Q, hQcentral, hQradius⟩ :=
    A.exists_orderThreePuncturedCollar_preimage_of_baseOrbit_cayley
      P.sourceData C z hzOuter hbase
  let FQ := A.orderThreePuncturedCollarToFilling P.radius Q
  have hFQcore : FQ ∈ A.orderThreeStarFillingCore := by
    change A.orderThreeFillingRadius P.radius FQ ≤ P.radius / 2
    rw [show FQ = A.orderThreePuncturedCollarToFilling P.radius Q from rfl,
      A.orderThreeFillingRadius_puncturedCollarToFilling, hQradius]
    exact hz.le
  refine ⟨FQ, hFQcore, ?_⟩
  change A.fourPieceStarGluingData.glueData.toGlueData.ι none C =
    A.fourPieceStarGluingData.glueData.toGlueData.ι (some 1)
      (A.orderThreePuncturedCollarToFilling P.radius Q)
  rw [← hQcentral]
  change
    A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
        none (A.starToCentral 1 Q) =
      A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
        (some 1) (A.starToFilling 1 Q)
  exact A.openEmbeddingStarData.toFourPieceStarGluingData_ι_toCentral_eq_ι_toFilling 1 Q

/-- A sufficiently small normalized-coordinate neighborhood of one is covered by the compact
half-core of the selected order-four filling. -/
public theorem exists_orderFourStarCore_coordinate_cover :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : A.CentralFamily,
      dist (A.centralBaseCoordinate C) 1 < ε →
        ∃ Q : A.starFillingType 2, Q ∈ A.starFillingCore 2 ∧
          A.fourPieceStarGluingData.glueData.toGlueData.ι none C =
            A.fourPieceStarGluingData.glueData.toGlueData.ι (some 2) Q := by
  let P := A.starSeparation.orderFour
  obtain ⟨ε, hε, hcover⟩ :=
    A.exists_orderFour_fullBaseCoordinate_ball_cayley
      (P.radius / 2) (half_pos P.radius_pos)
  refine ⟨ε, hε, ?_⟩
  intro C hC
  change dist (A.fullBaseOrbitHomeomorphComplex (A.centralBaseOrbit C)) 1 < ε at hC
  obtain ⟨z, hz, hbase⟩ := hcover (A.centralBaseOrbit C) hC
  have hzOuter : ‖(orderFourCayleyHomeomorph z).1‖ < P.radius :=
    hz.trans (half_lt_self P.radius_pos)
  obtain ⟨Q, hQcentral, hQradius⟩ :=
    A.exists_orderFourPuncturedCollar_preimage_of_baseOrbit_cayley
      P.sourceData C z hzOuter hbase
  let FQ := A.orderFourPuncturedCollarToFilling P.radius Q
  have hFQcore : FQ ∈ A.orderFourStarFillingCore := by
    change A.orderFourFillingRadius P.radius FQ ≤ P.radius / 2
    rw [show FQ = A.orderFourPuncturedCollarToFilling P.radius Q from rfl,
      A.orderFourFillingRadius_puncturedCollarToFilling, hQradius]
    exact hz.le
  refine ⟨FQ, hFQcore, ?_⟩
  change A.fourPieceStarGluingData.glueData.toGlueData.ι none C =
    A.fourPieceStarGluingData.glueData.toGlueData.ι (some 2)
      (A.orderFourPuncturedCollarToFilling P.radius Q)
  rw [← hQcentral]
  change
    A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
        none (A.starToCentral 2 Q) =
      A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
        (some 2) (A.starToFilling 2 Q)
  exact A.openEmbeddingStarData.toFourPieceStarGluingData_ι_toCentral_eq_ι_toFilling 2 Q

/-- One positive normalized-coordinate width works simultaneously for both compact elliptic
half-cores. -/
public theorem exists_ellipticStarCore_coordinate_cover :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : A.CentralFamily,
      A.centralBaseCoordinate C ∈ Metric.ball 0 ε ∪ Metric.ball 1 ε →
        ∃ i Q, Q ∈ A.starFillingCore i ∧
          A.fourPieceStarGluingData.glueData.toGlueData.ι none C =
            A.fourPieceStarGluingData.glueData.toGlueData.ι (some i) Q := by
  obtain ⟨ε₃, hε₃, hthree⟩ := A.exists_orderThreeStarCore_coordinate_cover
  obtain ⟨ε₄, hε₄, hfour⟩ := A.exists_orderFourStarCore_coordinate_cover
  refine ⟨min ε₃ ε₄, lt_min hε₃ hε₄, ?_⟩
  intro C hC
  rcases hC with hC | hC
  · obtain ⟨Q, hQcore, hQglue⟩ := hthree C (by
      exact hC.trans_le (min_le_left ε₃ ε₄))
    exact ⟨1, Q, hQcore, hQglue⟩
  · obtain ⟨Q, hQcore, hQglue⟩ := hfour C (by
      exact hC.trans_le (min_le_right ε₃ ε₄))
    exact ⟨2, Q, hQcore, hQglue⟩

/-- A filling point outside its half-radius core is identified in the concrete gluing with a
point of the central family. -/
public theorem fourPieceStarGluingData_filling_mem_core_or_central
    (i : Fin 3) (Q : A.starFillingType i) :
    Q ∈ A.starFillingCore i ∨ ∃ C : A.CentralFamily,
      A.fourPieceStarGluingData.glueData.toGlueData.ι (some i) Q =
        A.fourPieceStarGluingData.glueData.toGlueData.ι none C := by
  rcases A.starFilling_mem_core_or_range i Q with hcore | hcollar
  · exact Or.inl hcore
  · obtain ⟨x, rfl⟩ := hcollar
    right
    refine ⟨A.starToCentral i x, ?_⟩
    change
      A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
          (some i) (A.starToFilling i x) =
        A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
          none (A.starToCentral i x)
    exact (A.openEmbeddingStarData.toFourPieceStarGluingData_ι_toCentral_eq_ι_toFilling
      i x).symm

/-- Compactness of the actual glued carrier is reduced to the two genuinely outstanding
geometric facts: compactness of the cusp half-core and compact coverage of the central remainder
after the three half-cores are attached.  The two elliptic compactness inputs and all
filling-to-central coverage are discharged here. -/
public theorem fourPieceStarGluingData_gluedCompact_of_cuspCore_and_centralCore
    (centralCore : Set A.CentralFamily)
    (hcentralCompact : IsCompact centralCore)
    (hcuspCompact : IsCompact A.cuspStarFillingCore)
    (hcentralCover : ∀ C : A.CentralFamily,
      C ∈ centralCore ∨ ∃ i Q, Q ∈ A.starFillingCore i ∧
        A.fourPieceStarGluingData.glueData.toGlueData.ι none C =
          A.fourPieceStarGluingData.glueData.toGlueData.ι (some i) Q) :
    CompactSpace (GluedSpace A.fourPieceStarGluingData.glueData) := by
  apply A.fourPieceStarGluingData.gluedCompact_of_compact_cores
    centralCore A.starFillingCore hcentralCompact
  · intro i
    fin_cases i
    · exact hcuspCompact
    · exact A.orderThreeStarFillingCore_isCompact
    · exact A.orderFourStarFillingCore_isCompact
  · exact hcentralCover
  · exact A.fourPieceStarGluingData_filling_mem_core_or_central

/-- For a positive-width bounded base core, compactness of the concrete gluing is reduced to
compactness of the cusp half-core and coverage of the three central ends by the attached filling
cores.  Compactness of the central core and both elliptic filling cores is automatic. -/
public theorem fourPieceStarGluingData_gluedCompact_of_cuspCore_and_baseCore_cover
    (R ε : ℝ) (hε : 0 < ε)
    (hcuspCompact : IsCompact A.cuspStarFillingCore)
    (hcentralCover : ∀ C : A.CentralFamily,
      C ∈ A.centralBaseCompactCore R ε ∨ ∃ i Q, Q ∈ A.starFillingCore i ∧
        A.fourPieceStarGluingData.glueData.toGlueData.ι none C =
          A.fourPieceStarGluingData.glueData.toGlueData.ι (some i) Q) :
    CompactSpace (GluedSpace A.fourPieceStarGluingData.glueData) := by
  exact A.fourPieceStarGluingData_gluedCompact_of_cuspCore_and_centralCore
    (A.centralBaseCompactCore R ε)
    (A.centralBaseCompactCore_isCompact R ε hε)
    hcuspCompact hcentralCover

/-- With local cusp cocompactness proved, compactness of the concrete gluing is reduced only to
the fixed-radius coverage of the three central ends. -/
public theorem fourPieceStarGluingData_gluedCompact_of_baseCore_cover
    (R ε : ℝ) (hε : 0 < ε)
    (hcentralCover : ∀ C : A.CentralFamily,
      C ∈ A.centralBaseCompactCore R ε ∨ ∃ i Q, Q ∈ A.starFillingCore i ∧
        A.fourPieceStarGluingData.glueData.toGlueData.ι none C =
          A.fourPieceStarGluingData.glueData.toGlueData.ι (some i) Q) :
    CompactSpace (GluedSpace A.fourPieceStarGluingData.glueData) := by
  exact A.fourPieceStarGluingData_gluedCompact_of_cuspCore_and_baseCore_cover
    R ε hε A.cuspStarFillingCore_isCompact hcentralCover

/-- The elliptic end coverage and compactness inputs are now automatic.  To prove compactness of
the concrete four-piece gluing it suffices to cover the exterior of one normalized-coordinate
closed ball by the compact cusp half-core. -/
public theorem fourPieceStarGluingData_gluedCompact_of_cuspExteriorCover
    (R : ℝ)
    (hcuspExterior : ∀ C : A.CentralFamily,
      A.centralBaseCoordinate C ∉ Metric.closedBall 0 R →
        ∃ Q : A.starFillingType 0, Q ∈ A.starFillingCore 0 ∧
          A.fourPieceStarGluingData.glueData.toGlueData.ι none C =
            A.fourPieceStarGluingData.glueData.toGlueData.ι (some 0) Q) :
    CompactSpace (GluedSpace A.fourPieceStarGluingData.glueData) := by
  obtain ⟨ε, hε, helliptic⟩ := A.exists_ellipticStarCore_coordinate_cover
  apply A.fourPieceStarGluingData_gluedCompact_of_baseCore_cover R ε hε
  intro C
  by_cases hbounded : A.centralBaseCoordinate C ∈ Metric.closedBall 0 R
  · by_cases hellipticEnd :
        A.centralBaseCoordinate C ∈ Metric.ball 0 ε ∪ Metric.ball 1 ε
    · exact Or.inr (helliptic C hellipticEnd)
    · left
      change A.centralBaseOrbit C ∈ A.fullBaseCompactCore R ε
      change A.fullBaseOrbitHomeomorphComplex (A.centralBaseOrbit C) ∈
        Metric.closedBall 0 R \ (Metric.ball 0 ε ∪ Metric.ball 1 ε)
      exact ⟨hbounded, hellipticEnd⟩
  · obtain ⟨Q, hQcore, hQglue⟩ := hcuspExterior C hbounded
    exact Or.inr ⟨0, Q, hQcore, hQglue⟩

/-- If a central base orbit has a representative in the normalized cusp horodisc, then the
entire central torus point lies in the actual global cusp collar. -/
public theorem mem_cuspCollar_of_baseOrbit_eq_lift
    (C : A.CentralFamily) (s : ℂ)
    (hs : s ∈ cuspHalfPlane A.cuspCoordinate.height)
    (hq : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius)
    (hbase : A.centralBaseOrbit C =
      (Quotient.mk _ (A.cuspCoordinate.lift s) : A.FullBaseOrbitSpace)) :
    C ∈ puncturedGlobalCuspCollar A.starCuspWitness := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let _ := triangleSourceMulAction U
  let _ := regularFamilyDeckAction A.periods
  induction C using Quotient.inductionOn with
  | _ x =>
      rw [A.centralBaseOrbit_mk] at hbase
      have hrel := Quotient.exact hbase.symm
      change MulAction.orbitRel Delta UpperHalfPlane
        (A.cuspCoordinate.lift s) (regularTotalSpaceBase A.periods x).1 at hrel
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
      obtain ⟨g, hg⟩ := hrel
      let x' := regularFamilyDeckMap A.periods g x
      have hxbase : regularTotalSpaceBase A.periods x' =
          ⟨A.cuspCoordinate.lift s, A.starCuspWitness.lift_regular hs hq⟩ := by
        rw [regularTotalSpaceBase_familyDeckMap]
        apply Subtype.ext
        exact hg
      have hxregion : x' ∈ regularCuspFamilyRegion A.starCuspWitness := by
        change (regularTotalSpaceBase A.periods x').1 ∈
          normalizedCuspRegion A.cuspCoordinate
            A.starCuspWitness.localWitness.radius
        rw [hxbase]
        exact ⟨s, ⟨hs, hq⟩, rfl⟩
      refine ⟨x', hxregion, ?_⟩
      apply Quotient.sound
      change MulAction.orbitRel Delta (RegularTotalSpace A.periods) x' x
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      exact ⟨g, rfl⟩

/-- The exterior of a sufficiently large normalized-coordinate ball is covered, with the exact
gluing equality, by the compact half-core of the selected cusp filling. -/
public theorem exists_cuspStarCore_coordinate_exterior_cover :
    ∃ R : ℝ, 0 < R ∧ ∀ C : A.CentralFamily,
      R < ‖A.centralBaseCoordinate C‖ →
        ∃ Q : A.starFillingType 0, Q ∈ A.starFillingCore 0 ∧
          A.fourPieceStarGluingData.glueData.toGlueData.ι none C =
            A.fourPieceStarGluingData.glueData.toGlueData.ι (some 0) Q := by
  obtain ⟨R, hR, hexterior⟩ :=
    exists_normalizedModularCusp_preimage_of_large_coordinate A.starCuspWitness
  refine ⟨R, hR, ?_⟩
  intro C hC
  obtain ⟨s, hs, hqHalf, hmodular⟩ :=
    hexterior (A.centralBaseCoordinate C) hC
  have hsource :
      A.modular.sourceCoordinate.coordinate (A.cuspCoordinate.lift s) =
        A.centralBaseCoordinate C := by
    have hperiod := A.periods.modular_equation (A.cuspCoordinate.lift s)
    change normalizedJ (A.periods.tau (A.cuspCoordinate.lift s)) =
      1728 * A.modular.modularParameter.coordinate
        (A.cuspCoordinate.lift s) at hperiod
    rw [A.modular.induced_coordinate] at hperiod
    calc
      A.modular.sourceCoordinate.coordinate (A.cuspCoordinate.lift s) =
          normalizedJ (A.periods.tau (A.cuspCoordinate.lift s)) / 1728 := by
        rw [hperiod]
        ring
      _ = A.centralBaseCoordinate C := hmodular
  have hbase : A.centralBaseOrbit C =
      (Quotient.mk _ (A.cuspCoordinate.lift s) : A.FullBaseOrbitSpace) := by
    apply A.fullBaseOrbitHomeomorphComplex.injective
    change A.centralBaseCoordinate C =
      A.fullBaseOrbitHomeomorphComplex (Quotient.mk _ (A.cuspCoordinate.lift s))
    rw [A.fullBaseOrbitHomeomorphComplex_mk, hsource]
  have hqFull : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius :=
    hqHalf.trans (half_lt_self A.starCuspWitness.localWitness.radius_pos)
  have hmem : C ∈ puncturedGlobalCuspCollar A.starCuspWitness :=
    A.mem_cuspCollar_of_baseOrbit_eq_lift C s hs hqFull hbase
  rw [← puncturedLocalCuspQuotientMap_range A.starCuspWitness] at hmem
  obtain ⟨Q, hQC⟩ := hmem
  obtain ⟨a, rfl⟩ :=
    additiveCuspRadiusToPuncturedLocalCuspQuotient_surjective
      A.starCuspWitness Q
  let Qlocal :=
    additiveCuspRadiusToPuncturedLocalCuspQuotient A.starCuspWitness a
  have haHalfPlane : a.1.2 ∈ cuspHalfPlane A.cuspCoordinate.height :=
    additiveCuspRadiusCover_halfPlane
      A.starCuspWitness.localWitness.radius_le a
  have horbit :
      (Quotient.mk _ (A.cuspCoordinate.lift a.1.2) : A.FullBaseOrbitSpace) =
        Quotient.mk _ (A.cuspCoordinate.lift s) := by
    calc
      (Quotient.mk _ (A.cuspCoordinate.lift a.1.2) : A.FullBaseOrbitSpace) =
          A.centralBaseOrbit
            (puncturedLocalCuspQuotientMap A.starCuspWitness Qlocal) :=
        (A.centralBaseOrbit_puncturedCusp_additiveCuspRadiusToQuotient a).symm
      _ = A.centralBaseOrbit C := congrArg A.centralBaseOrbit hQC
      _ = Quotient.mk _ (A.cuspCoordinate.lift s) := hbase
  have hnorm := norm_cuspQ_eq_of_lift_orbit_eq A.starCuspWitness
    a.1.2 s haHalfPlane hs a.2 hqFull horbit
  let FQ := puncturedLocalCuspToFilling A.starCuspWitness Qlocal
  have hFQcore : FQ ∈ A.cuspStarFillingCore := by
    change actualLocalCuspFillingRadius A.starCuspWitness FQ ≤
      A.starCuspWitness.localWitness.radius / 2
    rw [show FQ = puncturedLocalCuspToFilling A.starCuspWitness Qlocal from rfl,
      actualLocalCuspFillingRadius_puncturedLocalCuspToFilling,
      A.puncturedLocalCuspRadius_additiveCuspRadiusToQuotient, hnorm]
    exact hqHalf.le
  refine ⟨FQ, hFQcore, ?_⟩
  change A.fourPieceStarGluingData.glueData.toGlueData.ι none C =
    A.fourPieceStarGluingData.glueData.toGlueData.ι (some 0)
      (puncturedLocalCuspToFilling A.starCuspWitness Qlocal)
  rw [← hQC]
  change
    A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
        none (A.starToCentral 0 Qlocal) =
      A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
        (some 0) (A.starToFilling 0 Qlocal)
  exact A.openEmbeddingStarData.toFourPieceStarGluingData_ι_toCentral_eq_ι_toFilling
    0 Qlocal

/-- The actual four-piece carrier is compact: the two elliptic half-cores cover neighborhoods of
the finite branch values, the cusp half-core covers the coordinate exterior, and the intervening
central base core is compact. -/
public theorem fourPieceStarGluingData_gluedCompact :
    CompactSpace (GluedSpace A.fourPieceStarGluingData.glueData) := by
  obtain ⟨R, hR, hcover⟩ := A.exists_cuspStarCore_coordinate_exterior_cover
  apply A.fourPieceStarGluingData_gluedCompact_of_cuspExteriorCover R
  intro C hC
  apply hcover C
  simpa [Metric.mem_closedBall, dist_zero_right] using hC

/-- The actual cusp collar graph in the selected four-piece star is closed. -/
public theorem fourPieceStarGluingData_cusp_collarPairRange_isClosed :
    IsClosed (A.fourPieceStarGluingData.collarPairRange 0) := by
  rw [fourPieceStarGluingData.eq_def,
    A.openEmbeddingStarData.collarPairRange_toFourPieceStarGluingData]
  change IsClosed (Set.range
    (fun Q : puncturedLocalCuspQuotient A.starCuspWitness =>
      (puncturedLocalCuspQuotientMap A.starCuspWitness Q,
        puncturedLocalCuspToFilling A.starCuspWitness Q)))
  exact A.cuspPuncturedCollarPairRange_isClosed

/-- The actual order-three collar graph in the selected four-piece star is closed. -/
public theorem fourPieceStarGluingData_orderThree_collarPairRange_isClosed :
    IsClosed (A.fourPieceStarGluingData.collarPairRange 1) := by
  rw [fourPieceStarGluingData.eq_def,
    A.openEmbeddingStarData.collarPairRange_toFourPieceStarGluingData]
  change IsClosed (Set.range (fun Q : Quotient (restrictedOrbitRel
    (orderThreeAffineFamilyAction A.periods)
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderThree.radius)) =>
    (A.orderThreePuncturedCollarToCentralFamily
        A.starSeparation.orderThree.sourceData Q,
      A.orderThreePuncturedCollarToFilling
        A.starSeparation.orderThree.radius Q)))
  exact A.orderThreePuncturedCollarPairRange_isClosed
    A.starSeparation.orderThree.radius_lt_one
    A.starSeparation.orderThree.sourceData

/-- The actual order-four collar graph in the selected four-piece star is closed. -/
public theorem fourPieceStarGluingData_orderFour_collarPairRange_isClosed :
    IsClosed (A.fourPieceStarGluingData.collarPairRange 2) := by
  rw [fourPieceStarGluingData.eq_def,
    A.openEmbeddingStarData.collarPairRange_toFourPieceStarGluingData]
  change IsClosed (Set.range (fun Q : Quotient (restrictedOrbitRel
    (orderFourAffineFamilyAction A.periods)
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
        A.starSeparation.orderFour.radius)) =>
    (A.orderFourPuncturedCollarToCentralFamily
        A.starSeparation.orderFour.sourceData Q,
      A.orderFourPuncturedCollarToFilling
        A.starSeparation.orderFour.radius Q)))
  exact A.orderFourPuncturedCollarPairRange_isClosed
    A.starSeparation.orderFour.radius_lt_one
    A.starSeparation.orderFour.sourceData

/-- The three proved piecewise Hausdorff results and the two closed elliptic graphs reduce
Hausdorffness of the actual four-piece carrier to closedness of its cusp graph alone. -/
public theorem fourPieceStarGluingData_gluedT2_of_cusp_collarPairRange_isClosed
    (hcusp : IsClosed (A.fourPieceStarGluingData.collarPairRange 0)) :
    T2Space (GluedSpace A.fourPieceStarGluingData.glueData) := by
  let _ : T2Space A.fourPieceStarGluingData.central := A.centralFamily_t2
  let _ (i : Fin 3) : T2Space (A.fourPieceStarGluingData.filling i) := by
    change T2Space (A.starFillingType i)
    exact A.starFilling_t2 i
  apply A.fourPieceStarGluingData.gluedT2_of_isClosed_collarPairRange
  intro i
  fin_cases i
  · exact hcusp
  · exact A.fourPieceStarGluingData_orderThree_collarPairRange_isClosed
  · exact A.fourPieceStarGluingData_orderFour_collarPairRange_isClosed

/-- The actual four-piece glued carrier is Hausdorff. -/
public theorem fourPieceStarGluingData_gluedT2 :
    T2Space (GluedSpace A.fourPieceStarGluingData.glueData) :=
  A.fourPieceStarGluingData_gluedT2_of_cusp_collarPairRange_isClosed
    A.fourPieceStarGluingData_cusp_collarPairRange_isClosed

/-- The analytic certificate for the actual four-piece star. -/
@[expose] public noncomputable def fourPieceStarBiholomorphicData :
    EstablishedBiholomorphicStarGluing.BiholomorphicFourPieceStarData
      A.fourPieceStarGluingData :=
  A.openEmbeddingStarBiholomorphicData.toBiholomorphicFourPieceStarData

/-- The concrete star has nonempty attaching collars. -/
public theorem fourPieceStarGluingData_nonemptyCentralCollar :
    ∀ i, Nonempty (A.fourPieceStarGluingData.centralCollar i) := by
  let _ (i : Fin 3) : Nonempty (A.openEmbeddingStarData.collarSource i) :=
    A.starCollarSource_nonempty i
  exact A.openEmbeddingStarData.toFourPieceStarGluingData_nonemptyCentralCollar

/-- Every attaching collar in the central piece of the concrete star is path connected. -/
public theorem fourPieceStarGluingData_pathConnectedCentralCollar (i : Fin 3) :
    PathConnectedSpace (A.fourPieceStarGluingData.centralCollar i) := by
  let _ : PathConnectedSpace (A.openEmbeddingStarData.collarSource i) := by
    change PathConnectedSpace (A.starCollarSourceType i)
    exact A.starCollarSource_pathConnected i
  change PathConnectedSpace (A.openEmbeddingStarData.centralCollar i)
  exact (A.openEmbeddingStarData.toCentralCollarHomeomorph i).surjective.pathConnectedSpace
    (A.openEmbeddingStarData.toCentralCollarHomeomorph i).continuous

/-- Every piece of the concrete four-piece diagram is connected. -/
public theorem fourPieceStarGluingData_connectedPiece :
    ∀ i, ConnectedSpace (A.fourPieceStarGluingData.glueData.U i) := by
  intro i
  cases i with
  | none => exact A.centralFamily_connected
  | some i => exact A.starFilling_connected i

/-- Every piece of the concrete four-piece diagram is second countable. -/
public theorem fourPieceStarGluingData_pieceSecondCountable :
    ∀ i, SecondCountableTopology (A.fourPieceStarGluingData.glueData.U i) := by
  intro i
  cases i with
  | none => exact A.centralFamily_secondCountable
  | some i => exact A.starFilling_secondCountable i

/-- The concrete complex atlases on the central family and all three fillings. -/
@[instance_reducible] public noncomputable def fourPieceStarComplexCharts :
    ∀ i, ChartedSpace ComplexModel (A.fourPieceStarGluingData.glueData.U i) := fun i ↦ by
  cases i with
  | none => exact A.centralFamilyComplexCharts
  | some i => exact A.starFillingComplexCharts i

/-- Every piece of the concrete four-piece diagram is path connected. -/
public theorem fourPieceStarGluingData_pathConnectedPiece :
    ∀ i, PathConnectedSpace (A.fourPieceStarGluingData.glueData.U i) := by
  intro i
  let _ : ChartedSpace ComplexModel
      (A.fourPieceStarGluingData.glueData.U i) :=
    A.fourPieceStarComplexCharts i
  let _ : ConnectedSpace (A.fourPieceStarGluingData.glueData.U i) :=
    A.fourPieceStarGluingData_connectedPiece i
  let _ : LocallyPathConnectedSpace
      (A.fourPieceStarGluingData.glueData.U i) :=
    ChartedSpace.locallyPathConnectedSpace ComplexModel
      (A.fourPieceStarGluingData.glueData.U i)
  exact PathConnectedSpace.of_locallyPathConnectedSpace

/-- Every piece of the concrete star is a complex three-manifold in its selected atlas. -/
public theorem fourPieceStar_pieceIsManifold :
    letI (i : Option (Fin 3)) := A.fourPieceStarComplexCharts i
    ∀ i : Option (Fin 3), IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.fourPieceStarGluingData.glueData.U i) := by
  let _ (i : Option (Fin 3)) := A.fourPieceStarComplexCharts i
  intro i
  cases i with
  | none => exact A.centralFamily_isManifold
  | some i => exact A.starFilling_isManifold i

/-- The topological carrier obtained by the paper's explicit four-piece gluing. -/
public abbrev GluedPaperCarrier :=
  GluedSpace A.fourPieceStarGluingData.glueData

end PaperAnalyticData

end

end SphereSixComplex.Geometry
