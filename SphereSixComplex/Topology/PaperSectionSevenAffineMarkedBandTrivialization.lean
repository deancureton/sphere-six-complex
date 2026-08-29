module

public import SphereSixComplex.Topology.PaperSectionSevenAffineBandTrivializationDefs
public import SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
public import SphereSixComplex.Geometry.PaperCentralEndCover
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Homotopy.Lifting

/-!
# The marked product trivialization of the affine central band

The unmarked statement `SectionSevenAffineCentralBandProductTrivialization` only pins the base
coordinate of the product homeomorphism, so its fibre coordinate is undetermined up to an
arbitrary fibrewise self-homeomorphism of the torus.  This module builds the trivialization from
scratch and marks it: relative to a continuous lift of the convex affine strip through the
regular-coordinate covering, the fibre coordinate is exactly the canonical real-period coordinate
of the central four-torus, the one fed to the finite central-fibre covers.
-/

@[expose] public section

noncomputable section

open Set Topology
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

variable (A : PaperAnalyticData)

/-- The affine vertical strip is open in the affine coordinate line. -/
public theorem sectionSevenAffineVerticalStrip_isOpen :
    IsOpen sectionSevenAffineVerticalStrip := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

/-- The affine vertical strip avoids the two elliptic coordinate values. -/
public theorem sectionSevenAffineVerticalStrip_subset :
    sectionSevenAffineVerticalStrip ⊆ ({0, 1} : Set ℂ)ᶜ := by
  rintro z ⟨hlow, hhigh⟩ hz
  rcases hz with hz | hz
  · rw [hz] at hlow
    norm_num at hlow
  · rw [Set.mem_singleton_iff.mp hz] at hhigh
    norm_num at hhigh

/-- The affine coordinate on the regular base is the exact full-deck covering, transported
through the regular-base preimage homeomorphism.  This repeats
`PaperAnalyticData.regularCoordinate_isCoveringMap`, which lives in a module that may not be
imported here without a cycle. -/
private theorem regularCoordinate_isCoveringMap' :
    IsCoveringMap A.regularCoordinate := by
  let e := A.regularBaseCoordinatePreimageHomeomorph
  let f := ({0, 1} : Set ℂ)ᶜ.restrictPreimage
    A.modular.sourceCoordinate.coordinate
  have hf : IsCoveringMap f :=
    A.modular.sourceCoordinate.regular_covering.isCoveringMap_restrictPreimage
  have hcomp : IsCoveringMap (f ∘ e) := hf.comp_homeomorph e
  convert hcomp using 1
  rfl

/-- A continuous lift of the convex affine strip through the regular-coordinate covering.  Such a
lift exists because the strip is convex, hence simply connected, and the affine coordinate on the
regular base is a covering map. -/
public structure SectionSevenAffineStripLift where
  /-- The lifted strip inside the regular upper-half-plane base. -/
  lift : C(sectionSevenAffineVerticalStrip,
    RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
  /-- The lift is a section of the affine regular coordinate. -/
  lift_coordinate : ∀ z : sectionSevenAffineVerticalStrip,
    (A.regularCoordinate (lift z) : ℂ) = (z : ℂ)

/-- The convex affine strip really does lift through the regular-coordinate covering. -/
public theorem sectionSevenAffineStripLift_nonempty :
    Nonempty A.SectionSevenAffineStripLift := by
  let _ : LocallyPathConnectedSpace sectionSevenAffineVerticalStrip :=
    sectionSevenAffineVerticalStrip_isOpen.locallyPathConnectedSpace
  let _ : ContractibleSpace sectionSevenAffineVerticalStrip :=
    sectionSevenAffineVerticalStripContractible
  let _ : SimplyConnectedSpace sectionSevenAffineVerticalStrip :=
    SimplyConnectedSpace.ofContractible _
  let f : C(sectionSevenAffineVerticalStrip, RegularCoordinateBase) :=
    ⟨fun z ↦ ⟨z.1, sectionSevenAffineVerticalStrip_subset z.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  let a₀ : sectionSevenAffineVerticalStrip :=
    ⟨sectionSevenAffineVerticalStrip_nonempty.some,
      sectionSevenAffineVerticalStrip_nonempty.some_mem⟩
  obtain ⟨e₀, he₀⟩ := A.regularCoordinate_surjective (f a₀)
  obtain ⟨L, hL, -⟩ :=
    A.regularCoordinate_isCoveringMap'.existsUnique_continuousMap_lifts f a₀ e₀ he₀
  exact ⟨⟨L, fun z ↦ congrArg Subtype.val (congrFun hL.2 z)⟩⟩

/-- A continuous section of a local homeomorphism, taken along an open injection, is itself an
open map.  This is the reason a lifted strip is an honest sheet of the regular covering. -/
public theorem isOpenMap_of_isLocalHomeomorph_lift
    {E X Y : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
    {p : E → X} (hp : IsLocalHomeomorph p) {s : Y → E} (hs : Continuous s)
    (hopen : IsOpenMap (p ∘ s)) :
    IsOpenMap s := by
  intro W hW
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨a, haW, rfl⟩
  obtain ⟨e, hea, hpe⟩ := hp (s a)
  set T : Set Y := W ∩ s ⁻¹' e.source with hT
  have haT : a ∈ T := ⟨haW, hea⟩
  have hTopen : IsOpen T := hW.inter (e.open_source.preimage hs)
  have himage : s '' T = e.source ∩ p ⁻¹' ((p ∘ s) '' T) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨t, htT, rfl⟩
      exact ⟨htT.2, ⟨t, htT, rfl⟩⟩
    · rintro y ⟨hy, ⟨t, htT, hpt⟩⟩
      refine ⟨t, htT, ?_⟩
      symm
      have hey : p y = p (s t) := hpt.symm
      rw [hpe] at hey
      exact e.injOn hy htT.2 hey
  refine ⟨s '' T, Set.image_mono Set.inter_subset_left, ?_, ⟨a, haT, rfl⟩⟩
  rw [himage]
  exact e.open_source.inter ((hopen T hTopen).preimage hp.continuous)

/-- The affine strip, included into the twice-punctured affine coordinate line. -/
public def stripInclusion (z : sectionSevenAffineVerticalStrip) : RegularCoordinateBase :=
  ⟨z.1, sectionSevenAffineVerticalStrip_subset z.2⟩

public theorem stripInclusion_continuous : Continuous stripInclusion :=
  continuous_subtype_val.subtype_mk _

public theorem stripInclusion_isOpenMap : IsOpenMap stripInclusion := by
  intro W hW
  have himage : stripInclusion '' W = Subtype.val ⁻¹' (Subtype.val '' W) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, hx⟩
      exact ⟨w, hw, Subtype.ext hx⟩
  rw [himage]
  exact (sectionSevenAffineVerticalStrip_isOpen.isOpenMap_subtype_val W hW).preimage
    continuous_subtype_val

/-- A point of the affine strip and a chosen point above it determine a unique continuous lift of
the entire strip. -/
public theorem existsUnique_sectionSevenAffineStripContinuousLift
    (a₀ : sectionSevenAffineVerticalStrip)
    (e₀ : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (he₀ : A.regularCoordinate e₀ = stripInclusion a₀) :
    ∃! L : C(sectionSevenAffineVerticalStrip,
      RegularBase (U := A.modular.modularParameter.toTriangleUniformization)),
      L a₀ = e₀ ∧ A.regularCoordinate ∘ L = stripInclusion := by
  let _ : LocallyPathConnectedSpace sectionSevenAffineVerticalStrip :=
    sectionSevenAffineVerticalStrip_isOpen.locallyPathConnectedSpace
  let _ : ContractibleSpace sectionSevenAffineVerticalStrip :=
    sectionSevenAffineVerticalStripContractible
  let _ : SimplyConnectedSpace sectionSevenAffineVerticalStrip :=
    SimplyConnectedSpace.ofContractible _
  let f : C(sectionSevenAffineVerticalStrip, RegularCoordinateBase) :=
    ⟨stripInclusion, stripInclusion_continuous⟩
  exact A.regularCoordinate_isCoveringMap'.existsUnique_continuousMap_lifts f a₀ e₀ he₀

namespace SectionSevenAffineStripLift

variable {A}

public theorem lift_comp_coordinate (L : A.SectionSevenAffineStripLift) :
    A.regularCoordinate ∘ L.lift = stripInclusion := by
  funext z
  exact Subtype.ext (L.lift_coordinate z)

/-- A lifted strip is an open sheet of the regular covering. -/
public theorem lift_isOpenMap (L : A.SectionSevenAffineStripLift) :
    IsOpenMap L.lift := by
  refine isOpenMap_of_isLocalHomeomorph_lift A.regularCoordinate_isLocalHomeomorph
    L.lift.continuous ?_
  rw [L.lift_comp_coordinate]
  exact stripInclusion_isOpenMap

public theorem lift_injective (L : A.SectionSevenAffineStripLift) :
    Function.Injective L.lift := by
  intro z w h
  apply Subtype.ext
  rw [← L.lift_coordinate z, ← L.lift_coordinate w, h]

end SectionSevenAffineStripLift

/-- Every integral period section is continuous on the regular base. -/
public theorem regularPeriodSection_continuous (a : IntegerPeriods) :
    Continuous fun b : RegularBase
        (U := A.modular.modularParameter.toTriangleUniformization) ↦
      periodVector (regularParameterMap A.periods b).1 a :=
  (periodSection_contMDiff A.periods a ⊤).continuous.comp continuous_subtype_val

/-- The fibrewise period translations of the regular family are homeomorphisms. -/
public theorem regularFamilyContinuousConstSMul :
    ContinuousConstSMul (FamilyPeriodGroup (regularParameterMap A.periods))
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
        ComplexTwoSpace) :=
  familyContinuousConstSMul _ (A.regularPeriodSection_continuous)

/-- The lattice quotient of the regular family is an open map. -/
public theorem regularProjection_isOpenMap :
    IsOpenMap (projection (regularParameterMap A.periods)) := by
  let _ := A.regularFamilyContinuousConstSMul
  exact (MulAction.isOpenQuotientMap_quotientMk
    (Γ := FamilyPeriodGroup (regularParameterMap A.periods))
    (T := RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace)).isOpenMap

/-- Rebuild a fixed real-period vector of the canonical central four-torus in the moving period
basis over a regular base point. -/
public def regularFixedToMoving
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (v : ComplexTwoSpace) : ComplexTwoSpace :=
  (fixedToMovingCover A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne (b.1, v)).2

/-- The canonical real-period coordinate of a vector in the moving period basis, expressed in the
fixed basis of the central four-torus. -/
public def regularMovingToFixed
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (w : ComplexTwoSpace) : ComplexTwoSpace :=
  (movingToFixedCover A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne (b.1, w)).2

@[simp]
public theorem regularMovingToFixed_regularFixedToMoving
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (v : ComplexTwoSpace) :
    A.regularMovingToFixed b (A.regularFixedToMoving b v) = v :=
  congrArg Prod.snd (movingToFixedCover_fixedToMovingCover A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne (b.1, v))

@[simp]
public theorem regularFixedToMoving_regularMovingToFixed
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (w : ComplexTwoSpace) :
    A.regularFixedToMoving b (A.regularMovingToFixed b w) = w :=
  congrArg Prod.snd (fixedToMovingCover_movingToFixedCover A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne (b.1, w))

public theorem regularFixedToMoving_injective
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :
    Function.Injective (A.regularFixedToMoving b) := by
  intro v v' h
  rw [← A.regularMovingToFixed_regularFixedToMoving b v,
    ← A.regularMovingToFixed_regularFixedToMoving b v', h]

/-- The canonical rebuild turns a fixed integral period into the corresponding moving integral
period. -/
public theorem regularFixedToMoving_period_add
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (n : IntegerPeriods) (v : ComplexTwoSpace) :
    A.regularFixedToMoving b
        (periodVector A.duplicatedSectionSevenBandParameter n + v) =
      periodVector (regularParameterMap A.periods b).1 n +
        A.regularFixedToMoving b v :=
  congrArg Prod.snd (fixedToMovingCover_period_add A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne b.1 n v)

/-- The point of the actual central family determined by a strip parameter and a fixed
real-period vector of the canonical central four-torus. -/
public def stripLiftCover (L : A.SectionSevenAffineStripLift)
    (z : sectionSevenAffineVerticalStrip) (v : ComplexTwoSpace) : A.CentralFamily :=
  A.centralQuotientProjection
    (projection (regularParameterMap A.periods)
      (L.lift z, A.regularFixedToMoving (L.lift z) v))

public theorem stripLiftCover_respects (L : A.SectionSevenAffineStripLift)
    (z : sectionSevenAffineVerticalStrip) (v v' : ComplexTwoSpace)
    (h : MulAction.orbitRel (PeriodGroup A.duplicatedSectionSevenBandParameter)
      ComplexTwoSpace v v') :
    A.stripLiftCover L z v = A.stripLiftCover L z v' := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  change (g.toAdd : ComplexTwoSpace) + v' = v at hg
  obtain ⟨n, hn⟩ := g.toAdd.2
  change periodVector A.duplicatedSectionSevenBandParameter n =
    (g.toAdd : ComplexTwoSpace) at hn
  have hv : v = periodVector A.duplicatedSectionSevenBandParameter n + v' := by
    rw [hn]
    exact hg.symm
  rw [stripLiftCover, stripLiftCover, hv, A.regularFixedToMoving_period_add]
  congr 1
  apply Quotient.sound
  refine ⟨Multiplicative.ofAdd n, ?_⟩
  rfl

/-- The marked map from the affine strip and the canonical central four-torus into the actual
central family. -/
public def stripLiftPoint (L : A.SectionSevenAffineStripLift)
    (z : sectionSevenAffineVerticalStrip)
    (t : AdditiveTorus A.duplicatedSectionSevenBandParameter) : A.CentralFamily :=
  Quotient.liftOn t (A.stripLiftCover L z) (A.stripLiftCover_respects L z)

@[simp]
public theorem stripLiftPoint_mk (L : A.SectionSevenAffineStripLift)
    (z : sectionSevenAffineVerticalStrip) (v : ComplexTwoSpace) :
    A.stripLiftPoint L z (Quotient.mk _ v) = A.stripLiftCover L z v :=
  rfl

@[simp]
public theorem centralFamilyCoordinate_stripLiftCover (L : A.SectionSevenAffineStripLift)
    (z : sectionSevenAffineVerticalStrip) (v : ComplexTwoSpace) :
    A.centralFamilyCoordinate (A.stripLiftCover L z v) = stripInclusion z := by
  rw [stripLiftCover, A.centralFamilyCoordinate_centralQuotientProjection]
  exact Subtype.ext (L.lift_coordinate z)

@[simp]
public theorem centralFamilyCoordinate_stripLiftPoint (L : A.SectionSevenAffineStripLift)
    (z : sectionSevenAffineVerticalStrip)
    (t : AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    A.centralFamilyCoordinate (A.stripLiftPoint L z t) = stripInclusion z := by
  induction t using Quotient.inductionOn with
  | _ v => exact A.centralFamilyCoordinate_stripLiftCover L z v

/-- The marked trivializing map from the affine strip times the canonical central four-torus into
the actual central family. -/
public def stripLiftMap (L : A.SectionSevenAffineStripLift) :
    sectionSevenAffineVerticalStrip ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter → A.CentralFamily :=
  fun p ↦ A.stripLiftPoint L p.1 p.2

public theorem stripLiftCover_continuous (L : A.SectionSevenAffineStripLift) :
    Continuous fun p : sectionSevenAffineVerticalStrip × ComplexTwoSpace ↦
      A.stripLiftCover L p.1 p.2 := by
  have hbase : Continuous fun p : sectionSevenAffineVerticalStrip × ComplexTwoSpace ↦
      ((L.lift p.1).1, p.2) :=
    (continuous_subtype_val.comp (L.lift.continuous.comp continuous_fst)).prodMk continuous_snd
  have hfib : Continuous fun p : sectionSevenAffineVerticalStrip × ComplexTwoSpace ↦
      A.regularFixedToMoving (L.lift p.1) p.2 :=
    continuous_snd.comp ((fixedToMovingCover_continuous A.periods
      A.modular.modularParameter.toTriangleUniformization.zOne).comp hbase)
  exact A.centralQuotientProjection_isLocalHomeomorph.continuous.comp
    (continuous_quot_mk.comp ((L.lift.continuous.comp continuous_fst).prodMk hfib))

/-- The lattice quotient in the torus variable is an open quotient map. -/
public theorem stripTorusQuotient_isOpenQuotientMap :
    IsOpenQuotientMap
      (Prod.map (id : sectionSevenAffineVerticalStrip → sectionSevenAffineVerticalStrip)
        (Quotient.mk (MulAction.orbitRel
          (PeriodGroup A.duplicatedSectionSevenBandParameter) ComplexTwoSpace))) :=
  IsOpenQuotientMap.id.prodMap
    (MulAction.isOpenQuotientMap_quotientMk
      (Γ := PeriodGroup A.duplicatedSectionSevenBandParameter) (T := ComplexTwoSpace))

public theorem stripLiftMap_continuous (L : A.SectionSevenAffineStripLift) :
    Continuous (A.stripLiftMap L) := by
  apply (A.stripTorusQuotient_isOpenQuotientMap).isQuotientMap.continuous_iff.mpr
  exact A.stripLiftCover_continuous L

/-- Fibrewise real-period change of basis along a lifted strip. -/
public def stripFixedToMovingHomeomorph (L : A.SectionSevenAffineStripLift) :
    sectionSevenAffineVerticalStrip × ComplexTwoSpace ≃ₜ
      sectionSevenAffineVerticalStrip × ComplexTwoSpace where
  toFun p := (p.1, A.regularFixedToMoving (L.lift p.1) p.2)
  invFun p := (p.1, A.regularMovingToFixed (L.lift p.1) p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by
    refine continuous_fst.prodMk ?_
    exact continuous_snd.comp ((fixedToMovingCover_continuous A.periods
      A.modular.modularParameter.toTriangleUniformization.zOne).comp
        ((continuous_subtype_val.comp (L.lift.continuous.comp continuous_fst)).prodMk
          continuous_snd))
  continuous_invFun := by
    refine continuous_fst.prodMk ?_
    exact continuous_snd.comp ((movingToFixedCover_continuous A.periods
      A.modular.modularParameter.toTriangleUniformization.zOne).comp
        ((continuous_subtype_val.comp (L.lift.continuous.comp continuous_fst)).prodMk
          continuous_snd))

public theorem stripLiftCover_isOpenMap (L : A.SectionSevenAffineStripLift) :
    IsOpenMap fun p : sectionSevenAffineVerticalStrip × ComplexTwoSpace ↦
      A.stripLiftCover L p.1 p.2 := by
  have hcomp : (fun p : sectionSevenAffineVerticalStrip × ComplexTwoSpace ↦
      A.stripLiftCover L p.1 p.2) =
      (A.centralQuotientProjection ∘ projection (regularParameterMap A.periods) ∘
        Prod.map (⇑L.lift) id) ∘ (A.stripFixedToMovingHomeomorph L) := rfl
  rw [hcomp]
  exact (A.centralQuotientProjection_isLocalHomeomorph.isOpenMap.comp
    (A.regularProjection_isOpenMap.comp (L.lift_isOpenMap.prodMap IsOpenMap.id))).comp
      (A.stripFixedToMovingHomeomorph L).isOpenMap

public theorem stripLiftMap_isOpenMap (L : A.SectionSevenAffineStripLift) :
    IsOpenMap (A.stripLiftMap L) := by
  intro W hW
  have hpre : IsOpen (Prod.map (id : sectionSevenAffineVerticalStrip →
      sectionSevenAffineVerticalStrip)
      (Quotient.mk (MulAction.orbitRel
        (PeriodGroup A.duplicatedSectionSevenBandParameter) ComplexTwoSpace)) ⁻¹' W) :=
    hW.preimage (A.stripTorusQuotient_isOpenQuotientMap).continuous
  have himage : A.stripLiftMap L '' W =
      (fun p : sectionSevenAffineVerticalStrip × ComplexTwoSpace ↦
        A.stripLiftCover L p.1 p.2) ''
        (Prod.map (id : sectionSevenAffineVerticalStrip → sectionSevenAffineVerticalStrip)
          (Quotient.mk (MulAction.orbitRel
            (PeriodGroup A.duplicatedSectionSevenBandParameter) ComplexTwoSpace)) ⁻¹' W) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨v, hv⟩ := Quotient.mk_surjective q.2
      refine ⟨(q.1, v), ?_, ?_⟩
      · change (q.1, Quotient.mk _ v) ∈ W
        rw [hv]
        exact hq
      · change A.stripLiftCover L q.1 v = A.stripLiftMap L q
        rw [stripLiftMap, ← hv]
        rfl
    · rintro _ ⟨p, hp, rfl⟩
      exact ⟨(p.1, Quotient.mk _ p.2), hp, rfl⟩
  rw [himage]
  exact A.stripLiftCover_isOpenMap L _ hpre

/-- The triangle group acts freely on the regular base. -/
public theorem regularSourceEquiv_eq_one_of_fixed (g : Delta)
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (h : regularSourceEquiv g b = b) : g = 1 := by
  let _ := regularSourceMulAction A.modular.modularParameter.toTriangleUniformization
  let _ : IsCancelSMul Delta
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    regularSource_isCancelSMul_of_fuchsian
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact IsCancelSMul.eq_one_of_smul (x := b) h

/-- Two points of a lifted strip with the same central-family image have the same strip parameter
and the same canonical torus coordinate. -/
public theorem stripLiftCover_inj (L : A.SectionSevenAffineStripLift)
    (z z' : sectionSevenAffineVerticalStrip) (v v' : ComplexTwoSpace)
    (h : A.stripLiftCover L z v = A.stripLiftCover L z' v') :
    z = z' ∧
      (Quotient.mk _ v : AdditiveTorus A.duplicatedSectionSevenBandParameter) =
        Quotient.mk _ v' := by
  have hz : z = z' := by
    have hcoord := congrArg A.centralFamilyCoordinate h
    rw [A.centralFamilyCoordinate_stripLiftCover, A.centralFamilyCoordinate_stripLiftCover]
      at hcoord
    have hval : (z : ℂ) = (z' : ℂ) :=
      congrArg (Subtype.val : RegularCoordinateBase → ℂ) hcoord
    exact Subtype.ext hval
  subst hz
  refine ⟨rfl, ?_⟩
  let _ := regularFamilyDeckAction A.periods
  have horbit : MulAction.orbitRel Delta (RegularTotalSpace A.periods)
      (projection (regularParameterMap A.periods)
        (L.lift z, A.regularFixedToMoving (L.lift z) v))
      (projection (regularParameterMap A.periods)
        (L.lift z, A.regularFixedToMoving (L.lift z) v')) := Quotient.exact h
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
  obtain ⟨g, hg⟩ := horbit
  change regularFamilyDeckMap A.periods g
    (projection (regularParameterMap A.periods)
      (L.lift z, A.regularFixedToMoving (L.lift z) v')) =
    projection (regularParameterMap A.periods)
      (L.lift z, A.regularFixedToMoving (L.lift z) v) at hg
  have hbase := congrArg (regularTotalSpaceBase A.periods) hg
  rw [regularTotalSpaceBase_familyDeckMap] at hbase
  have hgone : g = 1 := A.regularSourceEquiv_eq_one_of_fixed g (L.lift z) hbase
  subst hgone
  rw [regularFamilyDeckMap_one] at hg
  have hlattice : MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap A.periods))
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
        ComplexTwoSpace)
      (L.lift z, A.regularFixedToMoving (L.lift z) v')
      (L.lift z, A.regularFixedToMoving (L.lift z) v) := Quotient.exact hg
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hlattice
  obtain ⟨a, ha⟩ := hlattice
  have hsnd := congrArg Prod.snd ha
  rw [family_smul_snd] at hsnd
  have hveq : A.regularFixedToMoving (L.lift z)
      (periodVector A.duplicatedSectionSevenBandParameter a.coeff + v) =
      A.regularFixedToMoving (L.lift z) v' := by
    rw [A.regularFixedToMoving_period_add]
    exact hsnd
  have hv := A.regularFixedToMoving_injective (L.lift z) hveq
  refine (Quotient.sound ?_).symm
  exact ⟨Multiplicative.ofAdd
    (⟨periodVector A.duplicatedSectionSevenBandParameter a.coeff, ⟨a.coeff, rfl⟩⟩ :
      periodLattice A.duplicatedSectionSevenBandParameter), hv⟩

public theorem stripLiftMap_injective (L : A.SectionSevenAffineStripLift) :
    Function.Injective (A.stripLiftMap L) := by
  rintro ⟨z, t⟩ ⟨z', t'⟩ h
  obtain ⟨v, rfl⟩ := Quotient.mk_surjective t
  obtain ⟨v', rfl⟩ := Quotient.mk_surjective t'
  obtain ⟨hz, ht⟩ := A.stripLiftCover_inj L z z' v v' h
  exact Prod.ext hz ht

/-- The image of the marked trivializing map is exactly the actual central band. -/
public theorem range_stripLiftMap (L : A.SectionSevenAffineStripLift) :
    Set.range (A.stripLiftMap L) =
      {q : A.CentralFamily | (1 / 3 : ℝ) < (A.centralFamilyCoordinate q).1.re ∧
        (A.centralFamilyCoordinate q).1.re < 2 / 3} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨⟨z, t⟩, rfl⟩
    show (1 / 3 : ℝ) < (A.centralFamilyCoordinate (A.stripLiftPoint L z t)).1.re ∧
      (A.centralFamilyCoordinate (A.stripLiftPoint L z t)).1.re < 2 / 3
    rw [A.centralFamilyCoordinate_stripLiftPoint]
    exact z.2
  · intro q hq
    obtain ⟨r, rfl⟩ := A.centralQuotientProjection_surjective q
    obtain ⟨bw, rfl⟩ := Quotient.mk_surjective r
    have hcf : A.centralFamilyCoordinate (A.centralQuotientProjection
        (projection (regularParameterMap A.periods) bw)) = A.regularCoordinate bw.1 := rfl
    have hq' : (1 / 3 : ℝ) < (A.regularCoordinate bw.1).1.re ∧
        (A.regularCoordinate bw.1).1.re < 2 / 3 := by
      rw [← hcf]
      exact hq
    let z : sectionSevenAffineVerticalStrip := ⟨(A.regularCoordinate bw.1).1, hq'⟩
    have hcoord : A.regularCoordinate (L.lift z) = A.regularCoordinate bw.1 :=
      Subtype.ext (L.lift_coordinate z)
    obtain ⟨g, hgcoord⟩ :=
      (A.modular.sourceCoordinate.coordinate_eq_iff_orbit (L.lift z).1 bw.1.1).mp
        (congrArg (Subtype.val : RegularCoordinateBase → ℂ) hcoord)
    have hgb : regularSourceEquiv g (L.lift z) = bw.1 := by
      apply Subtype.ext
      rw [regularSourceEquiv_val,
        A.modular.modularParameter.toTriangleUniformization_sourceAction]
      exact hgcoord
    have hpt1 : (regularDeckMap A.periods g⁻¹ bw).1 = L.lift z := by
      change regularSourceEquiv g⁻¹ bw.1 = L.lift z
      rw [← hgb]
      apply Subtype.ext
      change A.modular.modularParameter.toTriangleUniformization.sourceAction g⁻¹ •
        (A.modular.modularParameter.toTriangleUniformization.sourceAction g •
          (L.lift z).1) = (L.lift z).1
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    refine ⟨(z, Quotient.mk _
      (A.regularMovingToFixed (L.lift z) (regularDeckMap A.periods g⁻¹ bw).2)), ?_⟩
    show A.stripLiftCover L z
        (A.regularMovingToFixed (L.lift z) (regularDeckMap A.periods g⁻¹ bw).2) = _
    rw [stripLiftCover, A.regularFixedToMoving_regularMovingToFixed]
    have hpair : (L.lift z, (regularDeckMap A.periods g⁻¹ bw).2) =
        regularDeckMap A.periods g⁻¹ bw := by
      rw [← hpt1]
    rw [hpair]
    have hdeck := A.centralQuotientProjection_familyDeckMap g⁻¹
      (Quotient.mk _ bw : RegularTotalSpace A.periods)
    rw [regularFamilyDeckMap_mk] at hdeck
    exact hdeck

public theorem stripLiftMap_isOpenEmbedding (L : A.SectionSevenAffineStripLift) :
    IsOpenEmbedding (A.stripLiftMap L) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap (A.stripLiftMap_continuous L)
    (A.stripLiftMap_injective L) (A.stripLiftMap_isOpenMap L)

/-- The actual central band inside the central family, in marked product coordinates. -/
public noncomputable def stripLiftHomeomorph (L : A.SectionSevenAffineStripLift) :
    sectionSevenAffineVerticalStrip ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter ≃ₜ
      {q : A.CentralFamily | (1 / 3 : ℝ) < (A.centralFamilyCoordinate q).1.re ∧
        (A.centralFamilyCoordinate q).1.re < 2 / 3} :=
  (A.stripLiftMap_isOpenEmbedding L).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (A.range_stripLiftMap L))

@[simp]
public theorem stripLiftHomeomorph_coe (L : A.SectionSevenAffineStripLift)
    (p : sectionSevenAffineVerticalStrip ×
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    (A.stripLiftHomeomorph L p : A.CentralFamily) = A.stripLiftMap L p :=
  rfl

/-- The open height band, as a subspace of the central image. -/
public noncomputable def centralHeightBandHomeomorph
    (height : A.sectionSevenEllipticCentralImage → ℝ) (lower upper : ℝ) :
    {x : A.sectionSevenEllipticCentralImage | lower < height x ∧ height x < upper} ≃ₜ
      ↥(centralHeightBand height lower upper) :=
  ((IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).toHomeomorph).trans
    (Homeomorph.setCongr (by
      ext x
      simp [centralHeightBand]))

/-- The affine central band, mapped into the actual central family. -/
public noncomputable def sectionSevenAffineCentralBandToCentralFamily
    (S : A.SectionSevenAffineCentralSeparation) :
    centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper → A.CentralFamily :=
  fun x ↦ A.sectionSevenEllipticCentralImageHomeomorph
    ((A.sectionSevenAffineCentralHeightSplit S).bandToCentralImage x)

public theorem sectionSevenAffineCentralBandToCentralFamily_injective
    (S : A.SectionSevenAffineCentralSeparation) :
    Function.Injective (A.sectionSevenAffineCentralBandToCentralFamily S) := by
  intro x y h
  have h' := A.sectionSevenEllipticCentralImageHomeomorph.injective h
  have hval : (x : A.SectionSevenEllipticInterior) = (y : A.SectionSevenEllipticInterior) :=
    congrArg (Subtype.val :
      A.sectionSevenEllipticCentralImage → A.SectionSevenEllipticInterior) h'
  exact Subtype.ext hval

/-- The affine central band identified with the marked product, relative to a lifted strip. -/
public noncomputable def sectionSevenAffineCentralBandProductHomeomorphOfLift
    (S : A.SectionSevenAffineCentralSeparation) (L : A.SectionSevenAffineStripLift) :
    sectionSevenAffineVerticalStrip ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter ≃ₜ
      centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper :=
  let eImage : {x : A.sectionSevenEllipticCentralImage |
      (1 / 3 : ℝ) < A.sectionSevenEllipticCentralHeight x ∧
        A.sectionSevenEllipticCentralHeight x < 2 / 3} ≃ₜ
      {q : A.CentralFamily | (1 / 3 : ℝ) < (A.centralFamilyCoordinate q).1.re ∧
        (A.centralFamilyCoordinate q).1.re < 2 / 3} :=
    A.sectionSevenEllipticCentralImageHomeomorph.subtype fun _ ↦ Iff.rfl
  (A.stripLiftHomeomorph L).trans (eImage.symm.trans
    (A.centralHeightBandHomeomorph A.sectionSevenEllipticCentralHeight (1 / 3) (2 / 3)))

public theorem sectionSevenAffineCentralBandProductHomeomorphOfLift_toCentralFamily
    (S : A.SectionSevenAffineCentralSeparation) (L : A.SectionSevenAffineStripLift)
    (p : sectionSevenAffineVerticalStrip ×
      AdditiveTorus A.duplicatedSectionSevenBandParameter) :
    A.sectionSevenAffineCentralBandToCentralFamily S
        (A.sectionSevenAffineCentralBandProductHomeomorphOfLift S L p) =
      A.stripLiftPoint L p.1 p.2 :=
  A.sectionSevenEllipticCentralImageHomeomorph.apply_symm_apply _

/-- Canonicity of the marking, read on the cover: over the lifted strip the marked fibre
coordinate of the class of `(b, w)` is exactly the class of the real-period coordinate
`movingToFixedCover` at the order-three elliptic point. -/
public theorem stripLiftPoint_regularMovingToFixed (L : A.SectionSevenAffineStripLift)
    (z : sectionSevenAffineVerticalStrip) (w : ComplexTwoSpace) :
    A.stripLiftPoint L z
        (Quotient.mk _ (A.regularMovingToFixed (L.lift z) w)) =
      A.centralQuotientProjection
        (projection (regularParameterMap A.periods) (L.lift z, w)) := by
  show A.stripLiftCover L z (A.regularMovingToFixed (L.lift z) w) = _
  rw [stripLiftCover, A.regularFixedToMoving_regularMovingToFixed]

/-- The marked product trivialization of the affine central band.  Unlike the unmarked statement
it pins both coordinates of the product homeomorphism: the base coordinate is the affine central
coordinate, and, relative to any continuous lift of the strip through the regular-coordinate
covering, the fibre coordinate is exactly the canonical real-period coordinate of the central
four-torus, the coordinate the finite central-fibre covers are applied to. -/
public def SectionSevenAffineCentralBandMarkedTrivialization
    (S : A.SectionSevenAffineCentralSeparation) : Prop :=
  ∀ L : A.SectionSevenAffineStripLift,
    ∃ e : centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper ≃ₜ
      sectionSevenAffineVerticalStrip ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter,
      (∀ x, (e x).1 = A.sectionSevenAffineCentralBandProjection S x) ∧
      (∀ p, A.sectionSevenAffineCentralBandToCentralFamily S (e.symm p) =
        A.stripLiftPoint L p.1 p.2)

/-- The actual central torus family over the convex affine strip is a marked product: the
real-period coordinates trivialize the varying lattice upstairs and the lifted simply connected
strip is an honest sheet of the regular-coordinate covering, so their assembly descends to a
global product homeomorphism with the canonical fibre coordinate. -/
public theorem establishedActualCentralBandMarkedTrivialization
    (S : A.SectionSevenAffineCentralSeparation) :
    A.SectionSevenAffineCentralBandMarkedTrivialization S := by
  intro L
  refine ⟨(A.sectionSevenAffineCentralBandProductHomeomorphOfLift S L).symm, ?_, ?_⟩
  · intro x
    have hkey := A.sectionSevenAffineCentralBandProductHomeomorphOfLift_toCentralFamily S L
      ((A.sectionSevenAffineCentralBandProductHomeomorphOfLift S L).symm x)
    rw [Homeomorph.apply_symm_apply] at hkey
    have hcoord := congrArg A.centralFamilyCoordinate hkey
    rw [A.centralFamilyCoordinate_stripLiftPoint] at hcoord
    apply Subtype.ext
    exact (congrArg (Subtype.val : RegularCoordinateBase → ℂ) hcoord).symm
  · intro p
    rw [Homeomorph.symm_symm]
    exact A.sectionSevenAffineCentralBandProductHomeomorphOfLift_toCentralFamily S L p

variable {A}

/-- Relative to a lifted strip the marking determines the trivialization completely: the fibre
coordinate is not left free. -/
public theorem sectionSevenAffineCentralBandMarkedTrivialization_unique
    {S : A.SectionSevenAffineCentralSeparation} (L : A.SectionSevenAffineStripLift)
    {e e' : centralHeightBand
        (A.sectionSevenAffineCentralHeightSplit S).height
        (A.sectionSevenAffineCentralHeightSplit S).lower
        (A.sectionSevenAffineCentralHeightSplit S).upper ≃ₜ
      sectionSevenAffineVerticalStrip ×
        AdditiveTorus A.duplicatedSectionSevenBandParameter}
    (he : ∀ p, A.sectionSevenAffineCentralBandToCentralFamily S (e.symm p) =
      A.stripLiftPoint L p.1 p.2)
    (he' : ∀ p, A.sectionSevenAffineCentralBandToCentralFamily S (e'.symm p) =
      A.stripLiftPoint L p.1 p.2) :
    e = e' := by
  have hsymm : ⇑e.symm = ⇑e'.symm := by
    funext p
    exact A.sectionSevenAffineCentralBandToCentralFamily_injective S ((he p).trans (he' p).symm)
  apply Homeomorph.ext
  intro x
  have h1 : e.symm (e x) = e'.symm (e x) := congrFun hsymm (e x)
  rw [e.symm_apply_apply] at h1
  calc e x = e' (e'.symm (e x)) := (e'.apply_symm_apply _).symm
    _ = e' x := by rw [← h1]

/-- The marked trivialization implies the previously axiomatized unmarked one. -/
public theorem SectionSevenAffineCentralBandMarkedTrivialization.toProductTrivialization
    {S : A.SectionSevenAffineCentralSeparation}
    (M : A.SectionSevenAffineCentralBandMarkedTrivialization S) :
    A.SectionSevenAffineCentralBandProductTrivialization S := by
  obtain ⟨L⟩ := A.sectionSevenAffineStripLift_nonempty
  obtain ⟨e, hbase, -⟩ := M L
  exact ⟨e, hbase⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
