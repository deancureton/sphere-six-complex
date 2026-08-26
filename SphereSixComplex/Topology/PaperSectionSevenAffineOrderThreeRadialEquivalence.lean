module

public import SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
public import SphereSixComplex.Topology.PaperSectionSevenAffineRegularBaseRadialEquivalence
public import SphereSixComplex.Topology.PaperSectionSevenAffineRegularLiftCarriers

/-!
# The order-three affine radial equivalence on the regular torus family

The regular base radial deformation is transported to the regular torus family by moving each
fibre point to the new base point through its canonical real period coordinates.  The resulting
deformation is equivariant for the full triangle-group deck action, so the inclusion of the
order-three affine disc lift into its half-plane lift is a deck-equivariant homotopy
equivalence.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization

variable (A : PaperAnalyticData)

/-- Rebuild a vector-cover point over a new base point through the canonical real period
coordinates. -/
public noncomputable def fiberTransferCover
    (w : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (p : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :
    RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace :=
  (w, (fullRankDomain (regularParameterMap A.periods w)).realEquiv
    (periodCoordinates (regularParameterMap A.periods p.1) p.2))

/-- The fibre transfer respects the varying-lattice orbit relation. -/
public theorem fiberTransferCover_orbitRel
    (w : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (p q : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace)
    (h : MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap A.periods)) _ p q) :
    MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap A.periods)) _
      (fiberTransferCover A w p) (fiberTransferCover A w q) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
  obtain ⟨a, rfl⟩ := h
  refine ⟨a, ?_⟩
  apply Prod.ext
  · rfl
  · have hpc : periodCoordinates (regularParameterMap A.periods q.1)
        (periodVector (regularParameterMap A.periods q.1).1 a.coeff + q.2) =
        integerToReal a.coeff +
          periodCoordinates (regularParameterMap A.periods q.1) q.2 := by
      change (fullRankDomain (regularParameterMap A.periods q.1)).realEquiv.symm
        (periodVector (regularParameterMap A.periods q.1).1 a.coeff + q.2) = _
      rw [map_add]
      congr 1
      exact periodCoordinates_periodVector _ a.coeff
    change periodVector (regularParameterMap A.periods w).1 a.coeff +
        (fullRankDomain (regularParameterMap A.periods w)).realEquiv
          (periodCoordinates (regularParameterMap A.periods q.1) q.2) =
      (fullRankDomain (regularParameterMap A.periods w)).realEquiv
        (periodCoordinates (regularParameterMap A.periods q.1)
          (periodVector (regularParameterMap A.periods q.1).1 a.coeff + q.2))
    rw [hpc, map_add, (fullRankDomain (regularParameterMap A.periods w)).map_integer]

/-- Move a point of the regular torus family into the fibre over a new base point, keeping its
canonical real period coordinates. -/
public noncomputable def fiberTransfer
    (w : RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :
    RegularTotalSpace A.periods → RegularTotalSpace A.periods :=
  Quotient.map (fiberTransferCover A w) (fiberTransferCover_orbitRel A w)

@[simp]
public theorem fiberTransfer_mk
    (w : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (p : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :
    A.fiberTransfer w (Quotient.mk _ p) = Quotient.mk _ (fiberTransferCover A w p) :=
  rfl

@[simp]
public theorem regularTotalSpaceBase_fiberTransfer
    (w : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (q : RegularTotalSpace A.periods) :
    regularTotalSpaceBase A.periods (A.fiberTransfer w q) = w := by
  induction q using Quotient.inductionOn with
  | _ p => rfl

@[simp]
public theorem fiberTransfer_base (q : RegularTotalSpace A.periods) :
    A.fiberTransfer (regularTotalSpaceBase A.periods q) q = q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    apply congrArg (Quotient.mk _)
    apply Prod.ext
    · rfl
    · exact (fullRankDomain (regularParameterMap A.periods p.1)).realEquiv.apply_symm_apply p.2

@[simp]
public theorem fiberTransfer_fiberTransfer
    (w₁ w₂ : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (q : RegularTotalSpace A.periods) :
    A.fiberTransfer w₂ (A.fiberTransfer w₁ q) = A.fiberTransfer w₂ q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    apply congrArg (Quotient.mk _)
    apply Prod.ext
    · rfl
    · exact congrArg (fullRankDomain (regularParameterMap A.periods w₂)).realEquiv
        ((fullRankDomain (regularParameterMap A.periods w₁)).realEquiv.symm_apply_apply _)

/-- The period transport of a vector written in real period coordinates. -/
public theorem periodTransport_realEquiv (g : Delta) (x : PeriodDomain) (c : RealPeriods) :
    periodTransport g x ((fullRankDomain x).realEquiv c) =
      (fullRankDomain (rhoParameters g x)).realEquiv (rhoLambdaReal g c) := by
  change (fullRankDomain (rhoParameters g x)).realEquiv
    (rhoLambdaReal g ((fullRankDomain x).realEquiv.symm
      ((fullRankDomain x).realEquiv c))) = _
  rw [(fullRankDomain x).realEquiv.symm_apply_apply]

/-- The period parameter of the regular base is equivariant for the deck action. -/
public theorem regularParameterMap_sourceEquiv (g : Delta)
    (w : RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :
    regularParameterMap A.periods (regularSourceEquiv g w) =
      rhoParameters g (regularParameterMap A.periods w) :=
  parameterMap_equivariant A.periods g w.1

/-- The fibre transfer is equivariant for the triangle-group deck action. -/
public theorem fiberTransfer_deck (g : Delta)
    (w : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (q : RegularTotalSpace A.periods) :
    A.fiberTransfer (regularSourceEquiv g w) (regularFamilyDeckMap A.periods g q) =
      regularFamilyDeckMap A.periods g (A.fiberTransfer w q) := by
  induction q using Quotient.inductionOn with
  | _ p =>
    apply congrArg (Quotient.mk _)
    apply Prod.ext
    · rfl
    · change (fullRankDomain (regularParameterMap A.periods (regularSourceEquiv g w))).realEquiv
          (periodCoordinates (regularParameterMap A.periods (regularSourceEquiv g p.1))
            (periodTransport g (regularParameterMap A.periods p.1) p.2)) =
        periodTransport g (regularParameterMap A.periods w)
          ((fullRankDomain (regularParameterMap A.periods w)).realEquiv
            (periodCoordinates (regularParameterMap A.periods p.1) p.2))
      rw [periodTransport_realEquiv, A.regularParameterMap_sourceEquiv,
        A.regularParameterMap_sourceEquiv, periodCoordinates_transport]

/-- Joint continuity of the fibre transfer on the vector cover. -/
public theorem fiberTransferCover_continuous :
    Continuous (fun x : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
        (RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
          ComplexTwoSpace) ↦ fiberTransferCover A x.1 x.2) := by
  apply Continuous.prodMk continuous_fst
  have h1 : Continuous (fun x : RegularBase
        (U := A.modular.modularParameter.toTriangleUniformization) ×
        (RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
          ComplexTwoSpace) ↦
      periodCoordinates (regularParameterMap A.periods x.2.1) x.2.2) :=
    (periodCoordinates_parameterMap_continuous A.periods).comp
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))
  have h2 := (periodRealLinear_parameterMap_continuous A.periods).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk h1)
  convert h2 using 1
  funext x
  rw [fullRankDomain.eq_def, FullRank.ofSetupInequalities_realEquiv_apply]
  rfl

/-- Joint continuity of the fibre transfer on the regular torus family. -/
public theorem fiberTransfer_continuous :
    Continuous (fun x : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      RegularTotalSpace A.periods ↦ A.fiberTransfer x.1 x.2) := by
  let _ := familyContinuousConstSMul (regularParameterMap A.periods)
    (fun a => (periodSection_contMDiff A.periods a 0).continuous.comp continuous_subtype_val)
  have hq : IsOpenQuotientMap (Prod.map
      (id : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) →
        RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
      (Quotient.mk _ :
        RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
          ComplexTwoSpace → RegularTotalSpace A.periods)) :=
    IsOpenQuotientMap.id.prodMap
      (MulAction.isOpenQuotientMap_quotientMk
        (Γ := FamilyPeriodGroup (regularParameterMap A.periods))
        (T := RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
          ComplexTwoSpace))
  apply hq.isQuotientMap.continuous_iff.mpr
  change Continuous (fun x : RegularBase
      (U := A.modular.modularParameter.toTriangleUniformization) ×
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
        ComplexTwoSpace) ↦
    (Quotient.mk _ (fiberTransferCover A x.1 x.2) : RegularTotalSpace A.periods))
  exact continuous_quot_mk.comp (fiberTransferCover_continuous A)

/-- The fibre transfer lands over the prescribed base region. -/
public theorem regularCoordinate_fiberTransfer_mem {S : Set RegularCoordinateBase}
    (w : coveringRegionPreimage A.regularCoordinate S) (q : RegularTotalSpace A.periods) :
    A.regularCoordinate (regularTotalSpaceBase A.periods (A.fiberTransfer w.1 q)) ∈ S := by
  rw [A.regularTotalSpaceBase_fiberTransfer]
  exact w.2

section OrderThree

variable {r : ℝ}

/-- The base point of a point of the order-three affine disc lift carrier. -/
public def orderThreeDiscLiftBase (q : (A.orderThreeAffineDiscLiftCarrier r).carrier) :
    coveringRegionPreimage A.regularCoordinate (orderThreeAffineDiscCoordinateRegion r) :=
  ⟨regularTotalSpaceBase A.periods q.1, q.2⟩

public theorem orderThreeDiscLiftBase_continuous :
    Continuous (A.orderThreeDiscLiftBase (r := r)) :=
  ((regularTotalSpaceBase_continuous A.periods).comp continuous_subtype_val).subtype_mk _

/-- The base point of a point of the order-three affine half-plane lift carrier. -/
public def orderThreeHalfPlaneLiftBase (q : A.orderThreeAffineHalfPlaneLiftCarrier.carrier) :
    coveringRegionPreimage A.regularCoordinate orderThreeAffineHalfPlaneCoordinateRegion :=
  ⟨regularTotalSpaceBase A.periods q.1, q.2⟩

public theorem orderThreeHalfPlaneLiftBase_continuous :
    Continuous A.orderThreeHalfPlaneLiftBase :=
  ((regularTotalSpaceBase_continuous A.periods).comp continuous_subtype_val).subtype_mk _

public theorem orderThreeDiscLiftBase_deck (g : Delta)
    (q : (A.orderThreeAffineDiscLiftCarrier r).carrier) :
    A.orderThreeDiscLiftBase (actionMap (A.orderThreeAffineDiscLiftAction r) g q) =
      actionMap (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant (orderThreeAffineDiscCoordinateRegion r)) g
        (A.orderThreeDiscLiftBase q) :=
  Subtype.ext (regularTotalSpaceBase_familyDeckMap A.periods g q.1)

public theorem orderThreeHalfPlaneLiftBase_deck (g : Delta)
    (q : A.orderThreeAffineHalfPlaneLiftCarrier.carrier) :
    A.orderThreeHalfPlaneLiftBase (actionMap A.orderThreeAffineHalfPlaneLiftAction g q) =
      actionMap (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant orderThreeAffineHalfPlaneCoordinateRegion) g
        (A.orderThreeHalfPlaneLiftBase q) :=
  Subtype.ext (regularTotalSpaceBase_familyDeckMap A.periods g q.1)

/-- The order-three affine radial deformation of the regular base, transported to the regular
torus family by the canonical real period coordinates. -/
public noncomputable def orderThreeAffineRadialLiftEquiv
    {s : ℝ} (hs : 0 < s) (hsr : s < r) (hr : r ≤ 2 / 3) :
    EquivariantHomotopyEquivData
      (A.orderThreeAffineDiscLiftAction r) A.orderThreeAffineHalfPlaneLiftAction where
  toFun :=
    { toFun := A.orderThreeAffineDiscLiftInclusion hr
      continuous_toFun := A.orderThreeAffineDiscLiftInclusion_continuous hr }
  invFun :=
    { toFun := fun q ↦ ⟨A.fiberTransfer
        ((A.orderThreeBaseRadialEquiv hs hsr hr).invFun
          (A.orderThreeHalfPlaneLiftBase q)).1 q.1,
        A.regularCoordinate_fiberTransfer_mem
          (S := orderThreeAffineDiscCoordinateRegion r) _ _⟩
      continuous_toFun :=
        (A.fiberTransfer_continuous.comp
          (((continuous_subtype_val.comp
            ((A.orderThreeBaseRadialEquiv hs hsr hr).invFun.continuous.comp
              A.orderThreeHalfPlaneLiftBase_continuous))).prodMk
            continuous_subtype_val)).subtype_mk _ }
  toFun_equivariant _ _ := rfl
  invFun_equivariant g y := by
    apply Subtype.ext
    change A.fiberTransfer
        ((A.orderThreeBaseRadialEquiv hs hsr hr).invFun
          (A.orderThreeHalfPlaneLiftBase
            (actionMap A.orderThreeAffineHalfPlaneLiftAction g y))).1
        (regularFamilyDeckMap A.periods g y.1) =
      regularFamilyDeckMap A.periods g
        (A.fiberTransfer ((A.orderThreeBaseRadialEquiv hs hsr hr).invFun
          (A.orderThreeHalfPlaneLiftBase y)).1 y.1)
    rw [A.orderThreeHalfPlaneLiftBase_deck,
      (A.orderThreeBaseRadialEquiv hs hsr hr).invFun_equivariant]
    exact A.fiberTransfer_deck g _ y.1
  leftInvHomotopy :=
    { toFun := fun tq ↦ ⟨A.fiberTransfer
        ((A.orderThreeBaseRadialEquiv hs hsr hr).leftInvHomotopy
          (tq.1, A.orderThreeDiscLiftBase tq.2)).1 tq.2.1,
        A.regularCoordinate_fiberTransfer_mem
          (S := orderThreeAffineDiscCoordinateRegion r) _ _⟩
      continuous_toFun :=
        (A.fiberTransfer_continuous.comp
          ((continuous_subtype_val.comp
            ((A.orderThreeBaseRadialEquiv hs hsr hr).leftInvHomotopy.continuous.comp
              (continuous_fst.prodMk
                (A.orderThreeDiscLiftBase_continuous.comp continuous_snd)))).prodMk
            (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      map_zero_left := fun q ↦ by
        apply Subtype.ext
        change A.fiberTransfer
          ((A.orderThreeBaseRadialEquiv hs hsr hr).leftInvHomotopy
            (0, A.orderThreeDiscLiftBase q)).1 q.1 = _
        rw [ContinuousMap.Homotopy.apply_zero]
        rfl
      map_one_left := fun q ↦ by
        apply Subtype.ext
        change A.fiberTransfer
          ((A.orderThreeBaseRadialEquiv hs hsr hr).leftInvHomotopy
            (1, A.orderThreeDiscLiftBase q)).1 q.1 = _
        rw [ContinuousMap.Homotopy.apply_one]
        exact A.fiberTransfer_base q.1 }
  rightInvHomotopy :=
    { toFun := fun tq ↦ ⟨A.fiberTransfer
        ((A.orderThreeBaseRadialEquiv hs hsr hr).rightInvHomotopy
          (tq.1, A.orderThreeHalfPlaneLiftBase tq.2)).1 tq.2.1,
        A.regularCoordinate_fiberTransfer_mem
          (S := orderThreeAffineHalfPlaneCoordinateRegion) _ _⟩
      continuous_toFun :=
        (A.fiberTransfer_continuous.comp
          ((continuous_subtype_val.comp
            ((A.orderThreeBaseRadialEquiv hs hsr hr).rightInvHomotopy.continuous.comp
              (continuous_fst.prodMk
                (A.orderThreeHalfPlaneLiftBase_continuous.comp continuous_snd)))).prodMk
            (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      map_zero_left := fun q ↦ by
        apply Subtype.ext
        change A.fiberTransfer
          ((A.orderThreeBaseRadialEquiv hs hsr hr).rightInvHomotopy
            (0, A.orderThreeHalfPlaneLiftBase q)).1 q.1 = _
        rw [ContinuousMap.Homotopy.apply_zero]
        rfl
      map_one_left := fun q ↦ by
        apply Subtype.ext
        change A.fiberTransfer
          ((A.orderThreeBaseRadialEquiv hs hsr hr).rightInvHomotopy
            (1, A.orderThreeHalfPlaneLiftBase q)).1 q.1 = _
        rw [ContinuousMap.Homotopy.apply_one]
        exact A.fiberTransfer_base q.1 }
  leftInvHomotopy_equivariant g t x := by
    apply Subtype.ext
    change A.fiberTransfer
        ((A.orderThreeBaseRadialEquiv hs hsr hr).leftInvHomotopy
          (t, A.orderThreeDiscLiftBase
            (actionMap (A.orderThreeAffineDiscLiftAction r) g x))).1
        (regularFamilyDeckMap A.periods g x.1) =
      regularFamilyDeckMap A.periods g
        (A.fiberTransfer ((A.orderThreeBaseRadialEquiv hs hsr hr).leftInvHomotopy
          (t, A.orderThreeDiscLiftBase x)).1 x.1)
    rw [A.orderThreeDiscLiftBase_deck,
      (A.orderThreeBaseRadialEquiv hs hsr hr).leftInvHomotopy_equivariant]
    exact A.fiberTransfer_deck g _ x.1
  rightInvHomotopy_equivariant g t y := by
    apply Subtype.ext
    change A.fiberTransfer
        ((A.orderThreeBaseRadialEquiv hs hsr hr).rightInvHomotopy
          (t, A.orderThreeHalfPlaneLiftBase
            (actionMap A.orderThreeAffineHalfPlaneLiftAction g y))).1
        (regularFamilyDeckMap A.periods g y.1) =
      regularFamilyDeckMap A.periods g
        (A.fiberTransfer ((A.orderThreeBaseRadialEquiv hs hsr hr).rightInvHomotopy
          (t, A.orderThreeHalfPlaneLiftBase y)).1 y.1)
    rw [A.orderThreeHalfPlaneLiftBase_deck,
      (A.orderThreeBaseRadialEquiv hs hsr hr).rightInvHomotopy_equivariant]
    exact A.fiberTransfer_deck g _ y.1

/-- The inclusion of the order-three affine disc lift into the order-three affine half-plane
lift is a deck-equivariant homotopy equivalence on the regular torus family. -/
public theorem exists_orderThreeAffineRadialEquiv (hr0 : 0 < r) (hr : r ≤ 2 / 3) :
    ∃ E : EquivariantHomotopyEquivData
        (A.orderThreeAffineDiscLiftAction r) A.orderThreeAffineHalfPlaneLiftAction,
      (E.toFun : (A.orderThreeAffineDiscLiftCarrier r).carrier →
        A.orderThreeAffineHalfPlaneLiftCarrier.carrier) =
          A.orderThreeAffineDiscLiftInclusion hr :=
  ⟨A.orderThreeAffineRadialLiftEquiv (s := r / 2) (by linarith) (by linarith) hr, rfl⟩

end OrderThree

end SphereSixComplex.Geometry.PaperAnalyticData
