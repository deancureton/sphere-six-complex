module

public import SphereSixComplex.Geometry.EllipticFixedPointCriterion
public import SphereSixComplex.Geometry.EllipticCayleyHomeomorph

/-!
# Actual analytic charts near the elliptic fibres

The Cayley coordinate gives the base chart.  The locally biholomorphic period-family quotient
then supplies local analytic parametrizations by the Cayley disc times the vector cover.
-/

open scoped Manifold ComplexConjugate ContDiff

namespace SphereSixComplex.Geometry.EllipticLocalTrivialization

open Complex SphereSixComplex.TriangleGroup SphereSixComplex.Periods
open SphereSixComplex.Geometry SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticFamilySpecialization

noncomputable section

/-- The open embedding that equips the unit disc with its natural complex manifold structure. -/
public theorem discValIsOpenEmbedding :
    Topology.IsOpenEmbedding ((↑) : ComplexUnitDisc → ℂ) :=
  (isOpen_lt continuous_norm continuous_const).isOpenEmbedding_subtypeVal

public instance complexUnitDiscNonempty : Nonempty ComplexUnitDisc := ⟨discCenter⟩

/-- The complex chart on the open unit disc induced by its inclusion into `ℂ`. -/
public noncomputable instance complexUnitDiscChartedSpace : ChartedSpace ℂ ComplexUnitDisc :=
  discValIsOpenEmbedding.singletonChartedSpace

/-- The open unit disc is a complex manifold. -/
public instance complexUnitDiscIsManifold :
    IsManifold (modelWithCornersSelf ℂ ℂ) ∞ ComplexUnitDisc :=
  discValIsOpenEmbedding.isManifold_singleton

public theorem cayleyDiscCoordinate_contMDiff (a : UpperHalfPlane) (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (cayleyDiscCoordinate a) := by
  have hcomp : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (((↑) : ComplexUnitDisc → ℂ) ∘ cayleyDiscCoordinate a) := by
    change ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (cayleyCoordinate a)
    exact contMDiff_of_mdifferentiable (cayleyCoordinate_mdifferentiable a) n
  exact hcomp.of_comp_isOpenEmbedding discValIsOpenEmbedding

public theorem cayleyInverseUpper_contMDiff (a : UpperHalfPlane) (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (cayleyInverseUpper a) := by
  have hval : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      ((↑) : ComplexUnitDisc → ℂ) :=
    contMDiff_isOpenEmbedding discValIsOpenEmbedding
  have hcomp : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (((↑) : UpperHalfPlane → ℂ) ∘ cayleyInverseUpper a) := by
    change ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (fun w : ComplexUnitDisc ↦ ((a : ℂ) - w.1 * conj (a : ℂ)) / (1 - w.1))
    exact (contMDiff_const.sub (hval.mul contMDiff_const)).div₀
      (contMDiff_const.sub hval) (by
        intro w h
        have hw : w.1 = 1 := (sub_eq_zero.mp h).symm
        have := w.2
        rw [hw] at this
        norm_num at this)
  exact hcomp.of_comp_isOpenEmbedding UpperHalfPlane.isOpenEmbedding_coe

/-- The Cayley homeomorphism is an actual biholomorphism for the natural disc manifold. -/
@[expose] public noncomputable def cayleyDiffeomorph (a : UpperHalfPlane) (n : WithTop ℕ∞) :
    UpperHalfPlane ≃ₘ^n⟮(modelWithCornersSelf ℂ ℂ), (modelWithCornersSelf ℂ ℂ)⟯
      ComplexUnitDisc where
  toEquiv := (cayleyHomeomorph a).toEquiv
  contMDiff_toFun := cayleyDiscCoordinate_contMDiff a n
  contMDiff_invFun := cayleyInverseUpper_contMDiff a n

/-- The order-three Cayley coordinate as a biholomorphism. -/
@[expose] public noncomputable def orderThreeCayleyDiffeomorph (n : WithTop ℕ∞) :
    UpperHalfPlane ≃ₘ^n⟮(modelWithCornersSelf ℂ ℂ), (modelWithCornersSelf ℂ ℂ)⟯
      ComplexUnitDisc :=
  cayleyDiffeomorph fuchsianOneFixedPoint n

/-- The order-four Cayley coordinate as a biholomorphism. -/
@[expose] public noncomputable def orderFourCayleyDiffeomorph (n : WithTop ℕ∞) :
    UpperHalfPlane ≃ₘ^n⟮(modelWithCornersSelf ℂ ℂ), (modelWithCornersSelf ℂ ℂ)⟯
      ComplexUnitDisc :=
  cayleyDiffeomorph fuchsianTwoFixedPoint n

/-- The order-three Cayley chart on the vector cover as a biholomorphism. -/
@[expose] public noncomputable def orderThreeCoverDiffeomorph (n : WithTop ℕ∞) :
    (UpperHalfPlane × ComplexTwoSpace) ≃ₘ^n⟮GlobalDeckTotalModel, GlobalDeckTotalModel⟯
      (ComplexUnitDisc × ComplexTwoSpace) :=
  (orderThreeCayleyDiffeomorph n).prodCongr
    (Diffeomorph.refl GlobalDeckFiberModel ComplexTwoSpace n)

/-- The order-four Cayley chart on the vector cover as a biholomorphism. -/
@[expose] public noncomputable def orderFourCoverDiffeomorph (n : WithTop ℕ∞) :
    (UpperHalfPlane × ComplexTwoSpace) ≃ₘ^n⟮GlobalDeckTotalModel, GlobalDeckTotalModel⟯
      (ComplexUnitDisc × ComplexTwoSpace) :=
  (orderFourCayleyDiffeomorph n).prodCongr
    (Diffeomorph.refl GlobalDeckFiberModel ComplexTwoSpace n)

/-- The order-three Cayley coordinate on the vector-bundle cover. -/
@[expose] public noncomputable def orderThreeCoverHomeomorph :
    (UpperHalfPlane × ComplexTwoSpace) ≃ₜ (ComplexUnitDisc × ComplexTwoSpace) :=
  orderThreeCayleyHomeomorph.prodCongr (Homeomorph.refl ComplexTwoSpace)

/-- The order-four Cayley coordinate on the vector-bundle cover. -/
@[expose] public noncomputable def orderFourCoverHomeomorph :
    (UpperHalfPlane × ComplexTwoSpace) ≃ₜ (ComplexUnitDisc × ComplexTwoSpace) :=
  orderFourCayleyHomeomorph.prodCongr (Homeomorph.refl ComplexTwoSpace)

@[simp]
public theorem orderThreeCayleyHomeomorph_fixedPoint :
    orderThreeCayleyHomeomorph fuchsianOneFixedPoint = discCenter := by
  apply Subtype.ext
  exact orderThreeCayley_fixedPoint

@[simp]
public theorem orderFourCayleyHomeomorph_fixedPoint :
    orderFourCayleyHomeomorph fuchsianTwoFixedPoint = discCenter := by
  apply Subtype.ext
  exact orderFourCayley_fixedPoint

@[simp]
public theorem orderThreeCayleyHomeomorph_symm_center :
    orderThreeCayleyHomeomorph.symm discCenter = fuchsianOneFixedPoint := by
  rw [← orderThreeCayleyHomeomorph_fixedPoint,
    orderThreeCayleyHomeomorph.symm_apply_apply]

@[simp]
public theorem orderFourCayleyHomeomorph_symm_center :
    orderFourCayleyHomeomorph.symm discCenter = fuchsianTwoFixedPoint := by
  rw [← orderFourCayleyHomeomorph_fixedPoint,
    orderFourCayleyHomeomorph.symm_apply_apply]

section FamilyCharts

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- The first deck generator written in Cayley base coordinates on the vector cover. -/
@[expose] public noncomputable def orderThreeChartDeckMap
    (p : ComplexUnitDisc × ComplexTwoSpace) :
    ComplexUnitDisc × ComplexTwoSpace :=
  (orderThreeDiscRotation p.1,
    periodTransport g₁ (parameterMap F (orderThreeCayleyHomeomorph.symm p.1)) p.2)

/-- The second deck generator written in Cayley base coordinates on the vector cover. -/
@[expose] public noncomputable def orderFourChartDeckMap
    (p : ComplexUnitDisc × ComplexTwoSpace) :
    ComplexUnitDisc × ComplexTwoSpace :=
  (orderFourDiscRotation p.1,
    periodTransport g₂ (parameterMap F (orderFourCayleyHomeomorph.symm p.1)) p.2)

/-- The first family deck transformation transported to the Cayley vector-cover chart. -/
@[expose] public noncomputable def orderThreeChartDeckEquiv :
    Equiv.Perm (ComplexUnitDisc × ComplexTwoSpace) :=
  orderThreeCoverHomeomorph.toEquiv.permCongr (deckEquiv F g₁)

/-- The second family deck transformation transported to the Cayley vector-cover chart. -/
@[expose] public noncomputable def orderFourChartDeckEquiv :
    Equiv.Perm (ComplexUnitDisc × ComplexTwoSpace) :=
  orderFourCoverHomeomorph.toEquiv.permCongr (deckEquiv F g₂)

public theorem orderThreeChartDeckEquiv_pow :
    orderThreeChartDeckEquiv F ^ 3 = 1 := by
  change (orderThreeCoverHomeomorph.toEquiv.permCongr (deckEquiv F g₁)) ^ 3 = 1
  have hdeck : (deckEquiv F g₁) ^ 3 = 1 := by
    change ((deckRepresentation F) g₁) ^ 3 = 1
    rw [← map_pow (deckRepresentation F) g₁, g₁_pow_three, map_one]
  change (orderThreeCoverHomeomorph.toEquiv.permCongrHom (deckEquiv F g₁)) ^ 3 = 1
  rw [← map_pow orderThreeCoverHomeomorph.toEquiv.permCongrHom, hdeck, map_one]

public theorem orderFourChartDeckEquiv_pow :
    orderFourChartDeckEquiv F ^ 4 = 1 := by
  change (orderFourCoverHomeomorph.toEquiv.permCongr (deckEquiv F g₂)) ^ 4 = 1
  have hdeck : (deckEquiv F g₂) ^ 4 = 1 := by
    change ((deckRepresentation F) g₂) ^ 4 = 1
    rw [← map_pow (deckRepresentation F) g₂, g₂_pow_four, map_one]
  change (orderFourCoverHomeomorph.toEquiv.permCongrHom (deckEquiv F g₂)) ^ 4 = 1
  rw [← map_pow orderFourCoverHomeomorph.toEquiv.permCongrHom, hdeck, map_one]

/-- The actual order-three cyclic action on the Cayley vector-cover chart. -/
@[expose] public noncomputable def orderThreeChartRepresentation :
    FiniteCyclic 3 →* Equiv.Perm (ComplexUnitDisc × ComplexTwoSpace) :=
  cyclicRepresentation 3 (orderThreeChartDeckEquiv F) (orderThreeChartDeckEquiv_pow F)

/-- The actual order-four cyclic action on the Cayley vector-cover chart. -/
@[expose] public noncomputable def orderFourChartRepresentation :
    FiniteCyclic 4 →* Equiv.Perm (ComplexUnitDisc × ComplexTwoSpace) :=
  cyclicRepresentation 4 (orderFourChartDeckEquiv F) (orderFourChartDeckEquiv_pow F)

@[simp]
public theorem orderThreeChartRepresentation_generator :
    orderThreeChartRepresentation F (cyclicGenerator 3) = orderThreeChartDeckEquiv F :=
  cyclicRepresentation_generator 3 (orderThreeChartDeckEquiv F)
    (orderThreeChartDeckEquiv_pow F)

@[simp]
public theorem orderFourChartRepresentation_generator :
    orderFourChartRepresentation F (cyclicGenerator 4) = orderFourChartDeckEquiv F :=
  cyclicRepresentation_generator 4 (orderFourChartDeckEquiv F)
    (orderFourChartDeckEquiv_pow F)

/-- At the centre, the Cayley-chart deck map is the actual order-three fibre transport. -/
@[simp]
public theorem orderThreeChartDeckMap_center
    (hzOne : U.zOne = fuchsianOneFixedPoint) (z : ComplexTwoSpace) :
    orderThreeChartDeckMap F (discCenter, z) =
      (discCenter, periodTransport g₁ (parameterMap F U.zOne) z) := by
  apply Prod.ext
  · apply Subtype.ext
    simp [orderThreeChartDeckMap, orderThreeDiscRotation, discScalarEquiv_apply_val,
      discCenter]
  · simp [orderThreeChartDeckMap, ← hzOne]

/-- At the centre, the Cayley-chart deck map is the actual order-four fibre transport. -/
@[simp]
public theorem orderFourChartDeckMap_center
    (hzTwo : U.zTwo = fuchsianTwoFixedPoint) (z : ComplexTwoSpace) :
    orderFourChartDeckMap F (discCenter, z) =
      (discCenter, periodTransport g₂ (parameterMap F U.zTwo) z) := by
  apply Prod.ext
  · apply Subtype.ext
    simp [orderFourChartDeckMap, orderFourDiscRotation, discScalarEquiv_apply_val,
      discCenter]
  · simp [orderFourChartDeckMap, ← hzTwo]

/-- The order-three chart action on the central vector cover descends to the already constructed
affine automorphism of the special torus fibre. -/
public theorem orderThreeChartDeckMap_center_mk
    (hzOne : U.zOne = fuchsianOneFixedPoint) (z : ComplexTwoSpace) :
    Quotient.mk _ (orderThreeChartDeckMap F (discCenter, z)).2 =
      orderThreeFiberAutomorphism F (Quotient.mk _ z) := by
  rw [orderThreeChartDeckMap_center F hzOne, orderThreeFiberAutomorphism_mk]

/-- The analogous descent to the order-four special-fibre automorphism. -/
public theorem orderFourChartDeckMap_center_mk
    (hzTwo : U.zTwo = fuchsianTwoFixedPoint) (z : ComplexTwoSpace) :
    Quotient.mk _ (orderFourChartDeckMap F (discCenter, z)).2 =
      orderFourFiberAutomorphism F (Quotient.mk _ z) := by
  rw [orderFourChartDeckMap_center F hzTwo, orderFourFiberAutomorphism_mk]

/-- Exact conjugacy of the first lifted deck generator by the Cayley cover chart. -/
public theorem orderThreeCover_conjugates_deckMap
    (hsource : U.sourceAction = fuchsianSourceAction)
    (p : ComplexUnitDisc × ComplexTwoSpace) :
    orderThreeCoverHomeomorph
        (deckMap F g₁ (orderThreeCoverHomeomorph.symm p)) =
      orderThreeChartDeckMap F p := by
  apply Prod.ext
  · change orderThreeCayleyHomeomorph
      (U.sourceAction g₁ • orderThreeCayleyHomeomorph.symm p.1) =
        orderThreeDiscRotation p.1
    rw [hsource, orderThreeCayleyHomeomorph_generator,
      orderThreeCayleyHomeomorph.apply_symm_apply]
  · rfl

/-- Exact conjugacy of the second lifted deck generator by the Cayley cover chart. -/
public theorem orderFourCover_conjugates_deckMap
    (hsource : U.sourceAction = fuchsianSourceAction)
    (p : ComplexUnitDisc × ComplexTwoSpace) :
    orderFourCoverHomeomorph
        (deckMap F g₂ (orderFourCoverHomeomorph.symm p)) =
      orderFourChartDeckMap F p := by
  apply Prod.ext
  · change orderFourCayleyHomeomorph
      (U.sourceAction g₂ • orderFourCayleyHomeomorph.symm p.1) =
        orderFourDiscRotation p.1
    rw [hsource, orderFourCayleyHomeomorph_generator,
      orderFourCayleyHomeomorph.apply_symm_apply]
  · rfl

/-- Under the explicit Fuchsian source identification, the transported order-three equivalence is
exactly the concrete varying-period chart formula. -/
public theorem orderThreeChartDeckEquiv_apply
    (hsource : U.sourceAction = fuchsianSourceAction)
    (p : ComplexUnitDisc × ComplexTwoSpace) :
    orderThreeChartDeckEquiv F p = orderThreeChartDeckMap F p := by
  change orderThreeCoverHomeomorph
      (deckMap F g₁ (orderThreeCoverHomeomorph.symm p)) = orderThreeChartDeckMap F p
  exact orderThreeCover_conjugates_deckMap F hsource p

/-- The analogous concrete formula for the transported order-four equivalence. -/
public theorem orderFourChartDeckEquiv_apply
    (hsource : U.sourceAction = fuchsianSourceAction)
    (p : ComplexUnitDisc × ComplexTwoSpace) :
    orderFourChartDeckEquiv F p = orderFourChartDeckMap F p := by
  change orderFourCoverHomeomorph
      (deckMap F g₂ (orderFourCoverHomeomorph.symm p)) = orderFourChartDeckMap F p
  exact orderFourCover_conjugates_deckMap F hsource p

/-- Cayley-disc parametrization of the varying torus family through its vector cover. -/
@[expose] public noncomputable def orderThreeFamilyParam
    (p : ComplexUnitDisc × ComplexTwoSpace) : TotalSpace (parameterMap F) :=
  Quotient.mk _ (orderThreeCoverHomeomorph.symm p)

/-- The analogous order-four parametrization. -/
@[expose] public noncomputable def orderFourFamilyParam
    (p : ComplexUnitDisc × ComplexTwoSpace) : TotalSpace (parameterMap F) :=
  Quotient.mk _ (orderFourCoverHomeomorph.symm p)

/-- The descended first family deck map has the explicit Cayley-chart formula. -/
public theorem orderThreeFamilyParam_equivariant
    (hsource : U.sourceAction = fuchsianSourceAction)
    (p : ComplexUnitDisc × ComplexTwoSpace) :
    familyDeckMap F g₁ (orderThreeFamilyParam F p) =
      orderThreeFamilyParam F (orderThreeChartDeckMap F p) := by
  change familyDeckMap F g₁ (Quotient.mk _ (orderThreeCoverHomeomorph.symm p)) =
    Quotient.mk _ (orderThreeCoverHomeomorph.symm (orderThreeChartDeckMap F p))
  rw [familyDeckMap_mk]
  apply congrArg (Quotient.mk _)
  apply orderThreeCoverHomeomorph.injective
  rw [orderThreeCoverHomeomorph.apply_symm_apply]
  exact orderThreeCover_conjugates_deckMap F hsource p

/-- The descended second family deck map has the explicit Cayley-chart formula. -/
public theorem orderFourFamilyParam_equivariant
    (hsource : U.sourceAction = fuchsianSourceAction)
    (p : ComplexUnitDisc × ComplexTwoSpace) :
    familyDeckMap F g₂ (orderFourFamilyParam F p) =
      orderFourFamilyParam F (orderFourChartDeckMap F p) := by
  change familyDeckMap F g₂ (Quotient.mk _ (orderFourCoverHomeomorph.symm p)) =
    Quotient.mk _ (orderFourCoverHomeomorph.symm (orderFourChartDeckMap F p))
  rw [familyDeckMap_mk]
  apply congrArg (Quotient.mk _)
  apply orderFourCoverHomeomorph.injective
  rw [orderFourCoverHomeomorph.apply_symm_apply]
  exact orderFourCover_conjugates_deckMap F hsource p

/-- The order-three cyclic chart action descends through the family parametrization to the global
family deck action. -/
public theorem orderThreeFamilyParam_generator_equivariant
    (hsource : U.sourceAction = fuchsianSourceAction)
    (p : ComplexUnitDisc × ComplexTwoSpace) :
    familyDeckMap F g₁ (orderThreeFamilyParam F p) =
      orderThreeFamilyParam F
        (orderThreeChartRepresentation F (cyclicGenerator 3) p) := by
  rw [orderThreeChartRepresentation_generator,
    orderThreeChartDeckEquiv_apply F hsource]
  exact orderThreeFamilyParam_equivariant F hsource p

/-- The analogous descent of the order-four cyclic chart action. -/
public theorem orderFourFamilyParam_generator_equivariant
    (hsource : U.sourceAction = fuchsianSourceAction)
    (p : ComplexUnitDisc × ComplexTwoSpace) :
    familyDeckMap F g₂ (orderFourFamilyParam F p) =
      orderFourFamilyParam F
        (orderFourChartRepresentation F (cyclicGenerator 4) p) := by
  rw [orderFourChartRepresentation_generator,
    orderFourChartDeckEquiv_apply F hsource]
  exact orderFourFamilyParam_equivariant F hsource p

section AnalyticLifts

variable [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]

/-- The genuine complex-analytic local chart obtained by inverting the family quotient at a point
of the order-three fibre.  Its source is an open neighbourhood in the torus family and its target
is an open neighbourhood in the vector cover. -/
@[expose] public noncomputable def orderThreeFamilyLocalDiffeomorph
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    PartialDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      (TotalSpace (parameterMap F)) (UpperHalfPlane × ComplexTwoSpace) ω :=
  (hprojection (U.zOne, v)).localInverse

/-- The genuine complex-analytic local chart at a point of the order-four fibre. -/
@[expose] public noncomputable def orderFourFamilyLocalDiffeomorph
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    PartialDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      (TotalSpace (parameterMap F)) (UpperHalfPlane × ComplexTwoSpace) ω :=
  (hprojection (U.zTwo, v)).localInverse

/-- The actual analytic local trivialization at a point of the order-three fibre, now with the
base written in the Cayley disc. -/
@[expose] public noncomputable def orderThreeFamilyCayleyLocalDiffeomorph
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    PartialDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      (TotalSpace (parameterMap F)) (ComplexUnitDisc × ComplexTwoSpace) ω :=
  (orderThreeFamilyLocalDiffeomorph F hprojection v).trans
    (orderThreeCoverDiffeomorph ω).toPartialDiffeomorph

/-- The analogous analytic local trivialization at a point of the order-four fibre. -/
@[expose] public noncomputable def orderFourFamilyCayleyLocalDiffeomorph
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    PartialDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      (TotalSpace (parameterMap F)) (ComplexUnitDisc × ComplexTwoSpace) ω :=
  (orderFourFamilyLocalDiffeomorph F hprojection v).trans
    (orderFourCoverDiffeomorph ω).toPartialDiffeomorph

/-- The actual local analytic lift from the torus family to its vector cover at a point of the
order-three fibre. -/
@[expose] public noncomputable def orderThreeLocalLift
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    TotalSpace (parameterMap F) → UpperHalfPlane × ComplexTwoSpace :=
  orderThreeFamilyLocalDiffeomorph F hprojection v

/-- The analogous lift at a point of the order-four fibre. -/
@[expose] public noncomputable def orderFourLocalLift
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    TotalSpace (parameterMap F) → UpperHalfPlane × ComplexTwoSpace :=
  orderFourFamilyLocalDiffeomorph F hprojection v

public theorem orderThreeFamilyLocalDiffeomorph_open_source
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    IsOpen (orderThreeFamilyLocalDiffeomorph F hprojection v).source :=
  (orderThreeFamilyLocalDiffeomorph F hprojection v).open_source

public theorem orderFourFamilyLocalDiffeomorph_open_source
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    IsOpen (orderFourFamilyLocalDiffeomorph F hprojection v).source :=
  (orderFourFamilyLocalDiffeomorph F hprojection v).open_source

public theorem orderThreeFamilyLocalDiffeomorph_center_mem_source
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    projection (parameterMap F) (U.zOne, v) ∈
      (orderThreeFamilyLocalDiffeomorph F hprojection v).source :=
  (hprojection (U.zOne, v)).localInverse_mem_source

public theorem orderFourFamilyLocalDiffeomorph_center_mem_source
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    projection (parameterMap F) (U.zTwo, v) ∈
      (orderFourFamilyLocalDiffeomorph F hprojection v).source :=
  (hprojection (U.zTwo, v)).localInverse_mem_source

public theorem orderThreeLocalLift_contMDiffAt
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω
      (orderThreeLocalLift F hprojection v)
      (projection (parameterMap F) (U.zOne, v)) :=
  (hprojection (U.zOne, v)).localInverse_contMDiffAt

public theorem orderFourLocalLift_contMDiffAt
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω
      (orderFourLocalLift F hprojection v)
      (projection (parameterMap F) (U.zTwo, v)) :=
  (hprojection (U.zTwo, v)).localInverse_contMDiffAt

/-- The local lift is a right inverse to the quotient projection near the chosen point of the
order-three fibre. -/
public theorem orderThreeLocalLift_eventually_right
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    Filter.EventuallyEq (nhds (projection (parameterMap F) (U.zOne, v)))
      ((projection (parameterMap F)) ∘ orderThreeLocalLift F hprojection v) id :=
  (hprojection (U.zOne, v)).localInverse_eventuallyEq_right

/-- The corresponding local right-inverse identity at the order-four fibre. -/
public theorem orderFourLocalLift_eventually_right
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    Filter.EventuallyEq (nhds (projection (parameterMap F) (U.zTwo, v)))
      ((projection (parameterMap F)) ∘ orderFourLocalLift F hprojection v) id :=
  (hprojection (U.zTwo, v)).localInverse_eventuallyEq_right

@[simp]
public theorem orderThreeLocalLift_center
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    orderThreeLocalLift F hprojection v
        (projection (parameterMap F) (U.zOne, v)) = (U.zOne, v) :=
  (hprojection (U.zOne, v)).localInverse_left_inv
    (hprojection (U.zOne, v)).localInverse_mem_target

@[simp]
public theorem orderFourLocalLift_center
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    orderFourLocalLift F hprojection v
        (projection (parameterMap F) (U.zTwo, v)) = (U.zTwo, v) :=
  (hprojection (U.zTwo, v)).localInverse_left_inv
    (hprojection (U.zTwo, v)).localInverse_mem_target

@[simp]
public theorem orderThreeCayleyLocalChart_center
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (hzOne : U.zOne = fuchsianOneFixedPoint)
    (v : ComplexTwoSpace) :
    orderThreeCoverDiffeomorph ω
        (orderThreeLocalLift F hprojection v
          (projection (parameterMap F) (U.zOne, v))) = (discCenter, v) := by
  rw [orderThreeLocalLift_center]
  rw [hzOne]
  apply Prod.ext
  · exact orderThreeCayleyHomeomorph_fixedPoint
  · rfl

@[simp]
public theorem orderFourCayleyLocalChart_center
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (hzTwo : U.zTwo = fuchsianTwoFixedPoint)
    (v : ComplexTwoSpace) :
    orderFourCoverDiffeomorph ω
        (orderFourLocalLift F hprojection v
          (projection (parameterMap F) (U.zTwo, v))) = (discCenter, v) := by
  rw [orderFourLocalLift_center]
  rw [hzTwo]
  apply Prod.ext
  · exact orderFourCayleyHomeomorph_fixedPoint
  · rfl

/-- The holomorphic scalar Cayley base coordinate obtained from the local analytic family lift. -/
@[expose] public noncomputable def orderThreeLocalBaseCoordinate
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace)
    (q : TotalSpace (parameterMap F)) : ℂ :=
  orderThreeCayley (orderThreeLocalLift F hprojection v q).1

/-- The order-four scalar base coordinate. -/
@[expose] public noncomputable def orderFourLocalBaseCoordinate
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace)
    (q : TotalSpace (parameterMap F)) : ℂ :=
  orderFourCayley (orderFourLocalLift F hprojection v q).1

public theorem orderThreeLocalBaseCoordinate_contMDiffAt
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    ContMDiffAt GlobalDeckTotalModel (modelWithCornersSelf ℂ ℂ) ω
      (orderThreeLocalBaseCoordinate F hprojection v)
      (projection (parameterMap F) (U.zOne, v)) := by
  exact (contMDiff_of_mdifferentiable
      (cayleyCoordinate_mdifferentiable fuchsianOneFixedPoint) ω).contMDiffAt.comp _
    (contMDiff_fst.contMDiffAt.comp _ (orderThreeLocalLift_contMDiffAt F hprojection v))

public theorem orderFourLocalBaseCoordinate_contMDiffAt
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    ContMDiffAt GlobalDeckTotalModel (modelWithCornersSelf ℂ ℂ) ω
      (orderFourLocalBaseCoordinate F hprojection v)
      (projection (parameterMap F) (U.zTwo, v)) := by
  exact (contMDiff_of_mdifferentiable
      (cayleyCoordinate_mdifferentiable fuchsianTwoFixedPoint) ω).contMDiffAt.comp _
    (contMDiff_fst.contMDiffAt.comp _ (orderFourLocalLift_contMDiffAt F hprojection v))

@[simp]
public theorem orderThreeLocalBaseCoordinate_center
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (hzOne : U.zOne = fuchsianOneFixedPoint)
    (v : ComplexTwoSpace) :
    orderThreeLocalBaseCoordinate F hprojection v
      (projection (parameterMap F) (U.zOne, v)) = 0 := by
  rw [orderThreeLocalBaseCoordinate, orderThreeLocalLift_center, hzOne,
    orderThreeCayley_fixedPoint]

@[simp]
public theorem orderFourLocalBaseCoordinate_center
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (hzTwo : U.zTwo = fuchsianTwoFixedPoint)
    (v : ComplexTwoSpace) :
    orderFourLocalBaseCoordinate F hprojection v
      (projection (parameterMap F) (U.zTwo, v)) = 0 := by
  rw [orderFourLocalBaseCoordinate, orderFourLocalLift_center, hzTwo,
    orderFourCayley_fixedPoint]

end AnalyticLifts

end FamilyCharts

end

end SphereSixComplex.Geometry.EllipticLocalTrivialization
