module

public import SphereSixComplex.Topology.PaperCuspAffineDeckQuotient

/-!
# The cusp boundary quotient covering

The rank-four period translations and the integral logarithm translations combine into the
semidirect boundary deck action dictated by cusp monodromy.  This file records that action and
isolates the two geometric properties needed to identify the actual boundary projection as its
quotient covering.
-/

@[expose] public section

noncomputable section

open Matrix Set Topology
open scoped ContDiff Manifold

namespace SphereSixComplex

open Geometry Geometry.ComplexTorus Geometry.CuspPuncturedCollarBridge
open Geometry.StandardInfiniteA2ToricModel

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspAnalyticFillingCollar
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.FamilyEquivariance
open SphereSixComplex.Geometry.EstablishedFuchsianCuspNeighborhood
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
variable {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

/-- The inverse angular turn conjugates a lattice translation by inverse cusp monodromy. -/
public theorem cuspBoundaryAngularTranslate_neg_one_latticeTranslate
    (W : ActualPuncturedCuspCollarWitness N M) (v : Lattice)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    cuspBoundaryAngularTranslate W (-1) (cuspBoundaryLatticeTranslate W v p) =
      cuspBoundaryLatticeTranslate W ((-paperCuspMonodromy) v)
        (cuspBoundaryAngularTranslate W (-1) p) := by
  have h := congrArg (cuspBoundaryAngularTranslate W (-1))
    (cuspBoundaryAngularTranslate_one_latticeTranslate W
      ((-paperCuspMonodromy) v) (cuspBoundaryAngularTranslate W (-1) p))
  have hinv : M₀ *ᵥ ((-paperCuspMonodromy) v) = v := by
    rw [← paperCuspMonodromy_apply, AddAut.neg_apply,
      paperCuspMonodromy.apply_symm_apply]
  rw [hinv] at h
  rw [← cuspBoundaryAngularTranslate_add,
    ← cuspBoundaryAngularTranslate_add] at h
  simpa using h.symm

/-- An arbitrary integral angular turn conjugates period translation by the corresponding
integral power of cusp monodromy. -/
public theorem cuspBoundaryAngularTranslate_latticeTranslate
    (W : ActualPuncturedCuspCollarWitness N M) (k : ℤ) (v : Lattice)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    cuspBoundaryAngularTranslate W k (cuspBoundaryLatticeTranslate W v p) =
      cuspBoundaryLatticeTranslate W ((k • paperCuspMonodromy) v)
        (cuspBoundaryAngularTranslate W k p) := by
  induction k using Int.induction_on generalizing v p with
  | zero => simp
  | succ i hi =>
      calc
        cuspBoundaryAngularTranslate W ((i : ℤ) + 1)
            (cuspBoundaryLatticeTranslate W v p) =
            cuspBoundaryAngularTranslate W (i : ℤ)
              (cuspBoundaryAngularTranslate W 1
                (cuspBoundaryLatticeTranslate W v p)) :=
          cuspBoundaryAngularTranslate_add W (i : ℤ) 1 _
        _ = cuspBoundaryAngularTranslate W (i : ℤ)
              (cuspBoundaryLatticeTranslate W (M₀ *ᵥ v)
                (cuspBoundaryAngularTranslate W 1 p)) := by
          rw [cuspBoundaryAngularTranslate_one_latticeTranslate]
        _ = cuspBoundaryLatticeTranslate W
              (((i : ℤ) • paperCuspMonodromy) (M₀ *ᵥ v))
              (cuspBoundaryAngularTranslate W (i : ℤ)
                (cuspBoundaryAngularTranslate W 1 p)) :=
          hi (M₀ *ᵥ v) (cuspBoundaryAngularTranslate W 1 p)
        _ = cuspBoundaryLatticeTranslate W
              ((((i : ℤ) + 1) • paperCuspMonodromy) v)
              (cuspBoundaryAngularTranslate W ((i : ℤ) + 1) p) := by
          rw [show ((i : ℤ) + 1) • paperCuspMonodromy =
              (i : ℤ) • paperCuspMonodromy + paperCuspMonodromy by
            rw [add_zsmul, one_zsmul],
            AddAut.add_apply, paperCuspMonodromy_apply,
            cuspBoundaryAngularTranslate_add]
  | pred i hi =>
      calc
        cuspBoundaryAngularTranslate W (- (i : ℤ) - 1)
            (cuspBoundaryLatticeTranslate W v p) =
            cuspBoundaryAngularTranslate W (- (i : ℤ))
              (cuspBoundaryAngularTranslate W (-1)
                (cuspBoundaryLatticeTranslate W v p)) := by
          rw [← cuspBoundaryAngularTranslate_add]
          congr 2
        _ = cuspBoundaryAngularTranslate W (- (i : ℤ))
              (cuspBoundaryLatticeTranslate W ((-paperCuspMonodromy) v)
                (cuspBoundaryAngularTranslate W (-1) p)) := by
          rw [cuspBoundaryAngularTranslate_neg_one_latticeTranslate]
        _ = cuspBoundaryLatticeTranslate W
              (((- (i : ℤ)) • paperCuspMonodromy) ((-paperCuspMonodromy) v))
              (cuspBoundaryAngularTranslate W (- (i : ℤ))
                (cuspBoundaryAngularTranslate W (-1) p)) :=
          hi ((-paperCuspMonodromy) v) (cuspBoundaryAngularTranslate W (-1) p)
        _ = cuspBoundaryLatticeTranslate W
              (((- (i : ℤ) - 1) • paperCuspMonodromy) v)
              (cuspBoundaryAngularTranslate W (- (i : ℤ) - 1) p) := by
          rw [show (- (i : ℤ) - 1) • paperCuspMonodromy =
              (- (i : ℤ)) • paperCuspMonodromy + (-paperCuspMonodromy) by
            rw [sub_eq_add_neg, add_zsmul, neg_one_zsmul],
            AddAut.add_apply]
          rw [← cuspBoundaryAngularTranslate_add]
          congr 2

/-- The combined semidirect cusp boundary action on normalized additive coordinates. -/
@[instance_reducible] public noncomputable def paperCuspBoundaryDeckAction
    (W : ActualPuncturedCuspCollarWitness N M) :
    MulAction paperCuspBoundaryDeck
      (additiveCuspRadiusCover W.localWitness.radius) where
  smul g p :=
    cuspBoundaryLatticeTranslate W g.left.toAdd
      (cuspBoundaryAngularTranslate W g.right.toAdd p)
  one_smul p := by
    change cuspBoundaryLatticeTranslate W 0
      (cuspBoundaryAngularTranslate W 0 p) = p
    rw [cuspBoundaryAngularTranslate_zero, cuspBoundaryLatticeTranslate_zero]
  mul_smul g h p := by
    change cuspBoundaryLatticeTranslate W
        ((g * h).left.toAdd)
        (cuspBoundaryAngularTranslate W (g * h).right.toAdd p) =
      cuspBoundaryLatticeTranslate W g.left.toAdd
        (cuspBoundaryAngularTranslate W g.right.toAdd
          (cuspBoundaryLatticeTranslate W h.left.toAdd
            (cuspBoundaryAngularTranslate W h.right.toAdd p)))
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right]
    change cuspBoundaryLatticeTranslate W
        (g.left.toAdd + (g.right.toAdd • paperCuspMonodromy) h.left.toAdd)
        (cuspBoundaryAngularTranslate W (g.right.toAdd + h.right.toAdd) p) = _
    rw [cuspBoundaryAngularTranslate_add,
      cuspBoundaryAngularTranslate_latticeTranslate,
      ← cuspBoundaryLatticeTranslate_add]

@[simp]
public theorem paperCuspBoundaryDeck_smul_apply
    (W : ActualPuncturedCuspCollarWitness N M) (g : paperCuspBoundaryDeck)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    letI := paperCuspBoundaryDeckAction W
    g • p = cuspBoundaryLatticeTranslate W g.left.toAdd
      (cuspBoundaryAngularTranslate W g.right.toAdd p) :=
  rfl

/-- Every combined boundary deck transformation is invisible under the actual boundary
projection. -/
public theorem additiveCuspBoundaryProjection_paperCuspBoundaryDeck_smul
    (W : ActualPuncturedCuspCollarWitness N M) (g : paperCuspBoundaryDeck)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    letI := paperCuspBoundaryDeckAction W
    additiveCuspBoundaryProjection W (g • p) = additiveCuspBoundaryProjection W p := by
  let _ := paperCuspBoundaryDeckAction W
  rw [paperCuspBoundaryDeck_smul_apply,
    additiveCuspBoundaryProjection_latticeTranslate,
    additiveCuspBoundaryProjection_angularTranslate]

/-- Equality in the actual boundary quotient determines the integral angular shift and a period
translation between additive representatives. -/
public theorem additiveCuspBoundaryProjection_eq_period_data
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : additiveCuspRadiusCover W.localWitness.radius)
    (h : additiveCuspBoundaryProjection W a = additiveCuspBoundaryProjection W b) :
    ∃ k : ℤ, a.1.2 = b.1.2 - k ∧ ∃ n : IntegerPeriods,
      periodVector (periodValues
          (assembledFuchsianPeriodFunctions E D).tau
          (assembledFuchsianPeriodFunctions E D).mu
          (assembledFuchsianPeriodFunctions E D).beta (N.lift a.1.2)) n + a.1.1 = b.1.1 := by
  have hglobal : additiveCuspCoverToGlobal W a = additiveCuspCoverToGlobal W b := by
    rw [← puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection,
      ← puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection]
    exact congrArg (puncturedLocalCuspQuotientMap W) h
  let F := assembledFuchsianPeriodFunctions E D
  let _ := regularFamilyDeckAction F
  have horbit := Quotient.exact hglobal
  change MulAction.orbitRel Delta (RegularTotalSpace F) _ _ at horbit
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
  obtain ⟨g, hg⟩ := horbit
  change regularFamilyDeckMap F g
      (regularCuspFamilyPoint N b.1.2
        (W.lift_regular
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b) b.2) b.1.1) =
    regularCuspFamilyPoint N a.1.2
      (W.lift_regular
        (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a) a.2) a.1.1 at hg
  have hbase := congrArg (regularTotalSpaceBase F) hg
  simp only [regularCuspFamilyPoint] at hbase
  have hmeet :
      ((E.modularParameter.toTriangleUniformization.sourceAction g • ·) ''
          normalizedCuspRegion N W.localWitness.radius ∩
        normalizedCuspRegion N W.localWitness.radius).Nonempty := by
    refine ⟨N.lift a.1.2, ?_, ?_⟩
    · refine ⟨N.lift b.1.2, ⟨b.1.2, ⟨?_, b.2⟩, rfl⟩, ?_⟩
      · exact additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b
      · exact congrArg Subtype.val hbase
    · exact ⟨a.1.2,
        ⟨additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a, a.2⟩, rfl⟩
  obtain ⟨k, rfl⟩ := W.translates_meet_only_parabolic g hmeet
  have hlift : N.lift (b.1.2 - k) = N.lift a.1.2 :=
    (lift_sub_int N b.1.2
      (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b) k).trans
        (congrArg Subtype.val hbase)
  have hsSub : b.1.2 - k ∈ cuspHalfPlane N.height := by
    simpa [sub_eq_add_neg] using cuspHalfPlane_add_int
      (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b) (-k)
  have hs : a.1.2 = b.1.2 - k := by
    calc
      a.1.2 = (((assembledFuchsianPeriodFunctions E D).tau (N.lift a.1.2) :
          UpperHalfPlane) : ℂ) :=
        (N.lift_tau a.1.2
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a)).symm
      _ = (((assembledFuchsianPeriodFunctions E D).tau (N.lift (b.1.2 - k)) :
          UpperHalfPlane) : ℂ) := congrArg (fun z ↦
        (((assembledFuchsianPeriodFunctions E D).tau z : UpperHalfPlane) : ℂ)) hlift.symm
      _ = b.1.2 - k := N.lift_tau (b.1.2 - k) hsSub
  have hinner := Quotient.exact hg
  change MulAction.orbitRel
      (FamilyPeriodGroup (regularParameterMap F)) _
      (regularDeckMap F (g₀ ^ k)
        (regularCuspBundlePoint N b.1.2
          (W.lift_regular
            (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b) b.2) b.1.1))
      (regularCuspBundlePoint N a.1.2
        (W.lift_regular
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a) a.2) a.1.1) at hinner
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hinner
  obtain ⟨n, hn⟩ := hinner
  have hsnd := congrArg Prod.snd hn
  rw [family_smul_snd] at hsnd
  change periodVector (regularParameterMap F _).1 n.coeff + a.1.1 =
    periodTransport (g₀ ^ k) _ b.1.1 at hsnd
  rw [periodTransport_gZero_zpow] at hsnd
  refine ⟨k, hs, n.coeff, ?_⟩
  simpa [F, regularParameterMap, regularCuspBundlePoint,
    AnalyticTorusFamily.parameterMap] using hsnd

/-- The fibres of the actual cusp boundary projection are exactly the orbits of the semidirect
boundary deck action. -/
public theorem additiveCuspBoundaryProjection_eq_iff_mem_paperCuspBoundaryDeck_orbit
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : additiveCuspRadiusCover W.localWitness.radius) :
    letI := paperCuspBoundaryDeckAction W
    additiveCuspBoundaryProjection W a = additiveCuspBoundaryProjection W b ↔
      a ∈ MulAction.orbit paperCuspBoundaryDeck b := by
  let _ := paperCuspBoundaryDeckAction W
  constructor
  · intro h
    obtain ⟨k, hs, n, hn⟩ := additiveCuspBoundaryProjection_eq_period_data W a b h
    rw [MulAction.mem_orbit_iff]
    refine ⟨(⟨Multiplicative.ofAdd (-n), Multiplicative.ofAdd k⟩ :
      paperCuspBoundaryDeck), ?_⟩
    rw [paperCuspBoundaryDeck_smul_apply]
    apply Subtype.ext
    apply Prod.ext
    · change periodVector (periodValues
          (assembledFuchsianPeriodFunctions E D).tau
          (assembledFuchsianPeriodFunctions E D).mu
          (assembledFuchsianPeriodFunctions E D).beta (N.lift (b.1.2 - k))) (-n) +
        b.1.1 = a.1.1
      rw [← hs, show periodVector (periodValues
          (assembledFuchsianPeriodFunctions E D).tau
          (assembledFuchsianPeriodFunctions E D).mu
          (assembledFuchsianPeriodFunctions E D).beta (N.lift a.1.2)) (-n) =
          -periodVector (periodValues
            (assembledFuchsianPeriodFunctions E D).tau
            (assembledFuchsianPeriodFunctions E D).mu
            (assembledFuchsianPeriodFunctions E D).beta (N.lift a.1.2)) n from
        (periodHom _).map_neg n, ← hn]
      abel
    · exact hs.symm
  · rintro ⟨g, rfl⟩
    exact additiveCuspBoundaryProjection_paperCuspBoundaryDeck_smul W g b

/-- The actual boundary projection is a quotient map independently of its deck-group
identification. -/
public theorem additiveCuspBoundaryProjection_isQuotientMap
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsQuotientMap (additiveCuspBoundaryProjection W) := by
  let q₁ : additiveCuspRadiusCover W.localWitness.radius →
      Quotient (Setoid.ker (denseCuspExponentialRadius W.localWitness.radius)) :=
    Quotient.mk _
  let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
  let q₂ : {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} →
      puncturedLocalCuspQuotient W := Quotient.mk _
  have hq₁ : IsQuotientMap q₁ := isQuotientMap_quotient_mk'
  have he : IsQuotientMap e := e.isQuotientMap
  have hq₂ : IsQuotientMap q₂ := isQuotientMap_quotient_mk'
  have hcomp := hq₂.comp (he.comp hq₁)
  convert hcomp using 1
  funext p
  rfl

/-- The combined semidirect boundary action is free. -/
public theorem paperCuspBoundaryDeckAction_isCancelSMul
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := paperCuspBoundaryDeckAction W
    IsCancelSMul paperCuspBoundaryDeck
      (additiveCuspRadiusCover W.localWitness.radius) := by
  let _ := paperCuspBoundaryDeckAction W
  constructor
  intro g h p hgh
  change cuspBoundaryLatticeTranslate W g.left.toAdd
      (cuspBoundaryAngularTranslate W g.right.toAdd p) =
    cuspBoundaryLatticeTranslate W h.left.toAdd
      (cuspBoundaryAngularTranslate W h.right.toAdd p) at hgh
  have hs := congrArg (fun q ↦ q.1.2) hgh
  change p.1.2 - (g.right.toAdd : ℂ) = p.1.2 - (h.right.toAdd : ℂ) at hs
  have hrightAdd : g.right.toAdd = h.right.toAdd := by
    exact_mod_cast sub_right_inj.mp hs
  have hright : g.right = h.right := Multiplicative.toAdd.injective hrightAdd
  have hzeta := congrArg (fun q ↦ q.1.1) hgh
  change periodVector (periodValues
        (assembledFuchsianPeriodFunctions E D).tau
        (assembledFuchsianPeriodFunctions E D).mu
        (assembledFuchsianPeriodFunctions E D).beta
          (N.lift (p.1.2 - (g.right.toAdd : ℂ)))) g.left.toAdd + p.1.1 =
      periodVector (periodValues
        (assembledFuchsianPeriodFunctions E D).tau
        (assembledFuchsianPeriodFunctions E D).mu
        (assembledFuchsianPeriodFunctions E D).beta
          (N.lift (p.1.2 - (h.right.toAdd : ℂ)))) h.left.toAdd + p.1.1 at hzeta
  rw [hrightAdd] at hzeta
  have hperiod := add_right_cancel hzeta
  let F := assembledFuchsianPeriodFunctions E D
  let x := periodValues F.tau F.mu F.beta
    (N.lift (p.1.2 - (h.right.toAdd : ℂ)))
  have hleftAdd : g.left.toAdd = h.left.toAdd :=
    periodHom_injective
      (FullRank.ofSetupInequalities x
        (F.setup_inequalities (N.lift (p.1.2 - (h.right.toAdd : ℂ))))) hperiod
  apply SemidirectProduct.ext
  · exact Multiplicative.toAdd.injective hleftAdd
  · exact hright

/-- Every rank-four boundary translation is continuous on the normalized additive cover. -/
public theorem cuspBoundaryLatticeTranslate_continuous
    (W : ActualPuncturedCuspCollarWitness N M) (v : Lattice) :
    Continuous (cuspBoundaryLatticeTranslate W v) := by
  let S := additiveCuspRadiusCover W.localWitness.radius
  let F := assembledFuchsianPeriodFunctions E D
  have hlift : Continuous (fun p : S ↦ N.lift p.1.2) :=
    N.lift_holomorphic.continuousOn.comp_continuous
      (continuous_snd.comp continuous_subtype_val)
      (fun p ↦ additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p)
  have hperiod : Continuous (fun p : S ↦
      periodVector (periodValues F.tau F.mu F.beta (N.lift p.1.2)) v) :=
    (periodSection_contMDiff F v 0).continuous.comp hlift
  apply Continuous.subtype_mk
  exact (hperiod.add (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_snd.comp continuous_subtype_val)

/-- Every integral logarithm translation is continuous on the normalized additive cover. -/
public theorem cuspBoundaryAngularTranslate_continuous
    (W : ActualPuncturedCuspCollarWitness N M) (k : ℤ) :
    Continuous (cuspBoundaryAngularTranslate W k) := by
  apply Continuous.subtype_mk
  exact (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).sub continuous_const)

/-- The combined semidirect cusp boundary action is continuous element by element. -/
public theorem paperCuspBoundaryDeckAction_continuousConstSMul
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := paperCuspBoundaryDeckAction W
    ContinuousConstSMul paperCuspBoundaryDeck
      (additiveCuspRadiusCover W.localWitness.radius) := by
  let _ := paperCuspBoundaryDeckAction W
  constructor
  intro g
  change Continuous (fun p ↦
    cuspBoundaryLatticeTranslate W g.left.toAdd
      (cuspBoundaryAngularTranslate W g.right.toAdd p))
  exact (cuspBoundaryLatticeTranslate_continuous W g.left.toAdd).comp
    (cuspBoundaryAngularTranslate_continuous W g.right.toAdd)

/-- Local injectivity of the analytic cusp filling map separates every nontrivial combined deck
translate. -/
public theorem paperCuspBoundaryDeckAction_locally_disjoint
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := paperCuspBoundaryDeckAction W
    ∀ p : additiveCuspRadiusCover W.localWitness.radius,
      ∃ U ∈ nhds p, ∀ g : paperCuspBoundaryDeck,
        ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  let _ := paperCuspBoundaryDeckAction W
  let _ : IsCancelSMul paperCuspBoundaryDeck
      (additiveCuspRadiusCover W.localWitness.radius) :=
    paperCuspBoundaryDeckAction_isCancelSMul W
  let _ := additiveCuspRadiusCoverCharts W.localWitness.radius
  let _ := actualLocalCuspFillingCharts W
  have hlift : IsLocalDiffeomorph (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (additiveCuspFillingLift W) := by
    convert additiveCuspExponentialPoint_isLocalDiffeomorph W using 1
    funext p
    exact additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius p
  have hproj := actualLocalCuspFilling_projection_isLocalDiffeomorph W
  have hcomp : IsLocalDiffeomorph (modelWithCornersSelf ℂ AdditiveCuspCover)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (fun p ↦ actualCuspFillingProjection W (additiveCuspFillingLift W p)) := by
    intro p
    exact IsLocalDiffeomorphAt.comp (modelWithCornersSelf ℂ ComplexModel)
      (actualLocalCuspFilling W) (hlift p) (hproj (additiveCuspFillingLift W p))
  intro p
  obtain ⟨U, hUopen, hpU, hUinj⟩ :=
    hcomp.isLocalHomeomorph.isLocallyInjective p
  refine ⟨U, hUopen.mem_nhds hpU, ?_⟩
  intro g hg
  obtain ⟨y, ⟨x, hxU, rfl⟩, hgxU⟩ := hg
  have hfill : actualCuspFillingProjection W (additiveCuspFillingLift W (g • x)) =
      actualCuspFillingProjection W (additiveCuspFillingLift W x) := by
    rw [← additiveCuspCoverSquare_commutes,
      ← additiveCuspCoverSquare_commutes,
      additiveCuspBoundaryProjection_paperCuspBoundaryDeck_smul]
  have hgx : g • x = x := hUinj hgxU hxU hfill
  exact isCancelSMul_iff_eq_one_of_smul_eq.mp (inferInstanceAs
    (IsCancelSMul paperCuspBoundaryDeck
      (additiveCuspRadiusCover W.localWitness.radius))) g x hgx

/-- The normalized additive cusp boundary projection is the quotient covering by the full
semidirect affine deck group. -/
public theorem additiveCuspBoundaryProjection_isQuotientCoveringMap
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := paperCuspBoundaryDeckAction W
    IsQuotientCoveringMap (additiveCuspBoundaryProjection W)
      paperCuspBoundaryDeck := by
  let _ := paperCuspBoundaryDeckAction W
  refine {
    __ := additiveCuspBoundaryProjection_isQuotientMap W
    continuous_const_smul :=
      (paperCuspBoundaryDeckAction_continuousConstSMul W).continuous_const_smul
    apply_eq_iff_mem_orbit :=
      additiveCuspBoundaryProjection_eq_iff_mem_paperCuspBoundaryDeck_orbit W _ _
    disjoint := paperCuspBoundaryDeckAction_locally_disjoint W
  }

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex

end
