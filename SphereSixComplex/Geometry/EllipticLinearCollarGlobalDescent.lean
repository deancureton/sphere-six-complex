module

public import SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
public import SphereSixComplex.Geometry.EllipticAffineGlobalSeparation
public import SphereSixComplex.Geometry.RegularTorusFamily
import all SphereSixComplex.TriangleGroup.Representation
import all SphereSixComplex.Geometry.GlobalTorusFamily

/-!
# Linear elliptic collars inside the punctured global family

The regular varying torus family is the open part of the unexcised varying torus family over
the regular source locus.  This module constructs that open embedding and uses it to compare a
small finite cyclic elliptic collar with the full linear triangle-group quotient.
-/

namespace SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent

open Filter Set Topology
open SphereSixComplex.LatticeData SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticLogarithmicGaugeDescent
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Geometry.EllipticAffineGlobalSeparation
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness

noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- Inclusion of the regular vector-bundle cover into the full vector-bundle cover. -/
@[expose] public def regularBundleInclusion :
    RegularBase (U := U) × ComplexTwoSpace → UpperHalfPlane × ComplexTwoSpace :=
  fun p => (p.1.1, p.2)

public theorem regularBundleInclusion_continuous :
    Continuous (regularBundleInclusion (U := U)) :=
  (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd

public theorem regularBundleInclusion_isOpenMap
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    IsOpenMap (regularBundleInclusion (U := U)) := by
  change IsOpenMap (Prod.map (fun z : RegularBase (U := U) => z.1) id)
  exact (isOpen_isRegularBasePoint hproper).isOpenMap_subtype_val.prodMap IsOpenMap.id

/-- The canonical map from the torus family over the regular base to the unexcised torus
family. -/
@[expose] public noncomputable def regularFamilyInclusion :
    RegularTotalSpace F → TotalSpace (parameterMap F) :=
  Quotient.map (regularBundleInclusion (U := U)) fun p q hpq => by
    change MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _ p q at hpq
    change MulAction.orbitRel (FamilyPeriodGroup (parameterMap F)) _
      (regularBundleInclusion p) (regularBundleInclusion q)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq ⊢
    obtain ⟨a, ha⟩ := hpq
    refine ⟨Multiplicative.ofAdd a.coeff, ?_⟩
    apply Prod.ext
    · exact congrArg (fun x => x.1.1) ha
    · change periodVector (parameterMap F q.1.1).1 a.coeff + q.2 = p.2
      have hs := congrArg Prod.snd ha
      rw [family_smul_snd] at hs
      simpa only [regularParameterMap.eq_def] using hs

@[simp]
public theorem regularFamilyInclusion_mk
    (p : RegularBase (U := U) × ComplexTwoSpace) :
    regularFamilyInclusion F (Quotient.mk _ p) =
      Quotient.mk _ (regularBundleInclusion p) :=
  rfl

public theorem regularFamilyInclusion_continuous :
    Continuous (regularFamilyInclusion F) := by
  rw [regularFamilyInclusion.eq_def]
  exact continuous_quot_lift _
    (continuous_quot_mk.comp (regularBundleInclusion_continuous (U := U)))

public theorem regularFamilyInclusion_injective :
    Function.Injective (regularFamilyInclusion F) := by
  intro q x hqx
  induction q using Quotient.inductionOn with
  | _ p =>
    induction x using Quotient.inductionOn with
    | _ y =>
      rw [regularFamilyInclusion_mk, regularFamilyInclusion_mk,
        Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hqx
      obtain ⟨a, ha⟩ := hqx
      apply Quotient.sound
      change MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _ p y
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨Multiplicative.ofAdd a.coeff, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst ha
      · change periodVector (regularParameterMap F y.1).1 a.coeff + y.2 = p.2
        have hs := congrArg Prod.snd ha
        rw [family_smul_snd] at hs
        exact hs

public theorem regularFamilyInclusion_isOpenMap
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    IsOpenMap (regularFamilyInclusion F) := by
  let _ := familyContinuousConstSMul (regularParameterMap F)
    (fun a => (periodSection_contMDiff F a 0).continuous.comp continuous_subtype_val)
  let _ := familyContinuousConstSMul (parameterMap F)
    (fun a => (periodSection_contMDiff F a 0).continuous)
  let qreg : RegularBase (U := U) × ComplexTwoSpace → RegularTotalSpace F :=
    quotientProjection
  have hqreg_continuous : Continuous qreg := by
    dsimp only [qreg]
    rw [quotientProjection.eq_def]
    exact continuous_quot_mk
  have hqreg_surjective : Function.Surjective qreg := by
    dsimp only [qreg]
    rw [quotientProjection.eq_def]
    exact Quotient.mk_surjective
  apply IsOpenMap.of_comp hqreg_continuous hqreg_surjective
  have hquotient : IsOpenMap
      (quotientProjection : UpperHalfPlane × ComplexTwoSpace →
        TotalSpace (parameterMap F)) := by
    let _ : Setoid (UpperHalfPlane × ComplexTwoSpace) :=
      MulAction.orbitRel (FamilyPeriodGroup (parameterMap F)) _
    rw [quotientProjection.eq_def]
    change IsOpenMap (Quotient.mk' : UpperHalfPlane × ComplexTwoSpace →
      Quotient (MulAction.orbitRel (FamilyPeriodGroup (parameterMap F)) _))
    exact isOpenMap_quotient_mk'_mul
  have hopen : IsOpenMap
      ((quotientProjection : UpperHalfPlane × ComplexTwoSpace →
        TotalSpace (parameterMap F)) ∘ regularBundleInclusion (U := U)) :=
    hquotient.comp
      (regularBundleInclusion_isOpenMap (U := U) hproper)
  convert hopen using 1
  funext p
  change regularFamilyInclusion F (quotientProjection p) =
    quotientProjection (regularBundleInclusion p)
  simpa only [quotientProjection.eq_def] using regularFamilyInclusion_mk F p

/-- The regular torus family is an open subspace of the unexcised torus family. -/
public theorem regularFamilyInclusion_isOpenEmbedding
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    IsOpenEmbedding (regularFamilyInclusion F) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (regularFamilyInclusion_continuous F)
    (regularFamilyInclusion_injective F)
    (regularFamilyInclusion_isOpenMap F hproper)

public theorem familyTotalSpaceBase_regularFamilyInclusion
    (q : RegularTotalSpace F) :
    familyTotalSpaceBase F (regularFamilyInclusion F q) =
      (regularTotalSpaceBase F q).1 := by
  induction q using Quotient.inductionOn with
  | _ p =>
    rw [regularFamilyInclusion_mk, familyTotalSpaceBase_mk,
      regularTotalSpaceBase_mk]
    rfl

public theorem regularFamilyInclusion_range :
    Set.range (regularFamilyInclusion F) =
      {q : TotalSpace (parameterMap F) |
        IsRegularBasePoint (U := U) (familyTotalSpaceBase F q)} := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    change IsRegularBasePoint (U := U)
      (familyTotalSpaceBase F (regularFamilyInclusion F x))
    rw [familyTotalSpaceBase_regularFamilyInclusion]
    exact (regularTotalSpaceBase F x).property
  · intro hq
    induction q using Quotient.inductionOn with
    | _ p =>
      refine ⟨Quotient.mk _ (⟨p.1, ?_⟩, p.2), ?_⟩
      · change IsRegularBasePoint (U := U) (familyTotalSpaceBase F (Quotient.mk _ p)) at hq
        simpa only [familyTotalSpaceBase_mk] using hq
      · rw [regularFamilyInclusion_mk]
        rfl

/-- The torus family over the regular base is homeomorphic to the regular open part of the
unexcised family. -/
@[expose] public noncomputable def regularFamilyPartHomeomorph
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    RegularTotalSpace F ≃ₜ
      {q : TotalSpace (parameterMap F) |
        IsRegularBasePoint (U := U) (familyTotalSpaceBase F q)} :=
  (regularFamilyInclusion_isOpenEmbedding F hproper).toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (regularFamilyInclusion_range F))

@[simp]
public theorem regularFamilyPartHomeomorph_apply
    (hproper : SourceActionProperlyDiscontinuous (U := U)) (q : RegularTotalSpace F) :
    (regularFamilyPartHomeomorph F hproper q).1 = regularFamilyInclusion F q :=
  rfl

public theorem regularFamilyInclusion_regularFamilyDeckMap
    (g : Delta) (q : RegularTotalSpace F) :
    regularFamilyInclusion F (regularFamilyDeckMap F g q) =
      familyDeckMap F g (regularFamilyInclusion F q) := by
  induction q using Quotient.inductionOn with
  | _ p =>
    rw [regularFamilyDeckMap_mk, regularFamilyInclusion_mk,
      regularFamilyInclusion_mk, familyDeckMap_mk]
    rfl

/-- The two elliptic fixed points lie in distinct orbits of the explicit Fuchsian action. -/
public theorem fuchsianTwo_orbit_ne_one (g : Delta) :
    fuchsianSourceAction g • fuchsianTwoFixedPoint ≠ fuchsianOneFixedPoint := by
  intro hg
  have hinv : fuchsianSourceAction g⁻¹ • fuchsianOneFixedPoint =
      fuchsianTwoFixedPoint := by
    calc
      fuchsianSourceAction g⁻¹ • fuchsianOneFixedPoint =
          fuchsianSourceAction g⁻¹ •
            (fuchsianSourceAction g • fuchsianTwoFixedPoint) := congrArg _ hg.symm
      _ = fuchsianTwoFixedPoint := by rw [map_inv, inv_smul_smul]
  have hfixed : fuchsianSourceAction (g * g₂ * g⁻¹) • fuchsianOneFixedPoint =
      fuchsianOneFixedPoint := by
    rw [map_mul, map_mul, mul_smul, mul_smul, hinv,
      fuchsianTwoFixedPoint_fixed, hg]
  obtain ⟨a, ha⟩ := establishedFuchsianOneStabilizerExact (g * g₂ * g⁻¹) |>.mp hfixed
  let retractThree : Delta →* CyclicThree :=
    Monoid.Coprod.lift (MonoidHom.id CyclicThree) 1
  have haone : a = 1 := by
    have hretract := congrArg retractThree ha
    simpa [retractThree, SphereSixComplex.TriangleGroup.g₂.eq_def,
      mul_assoc] using hretract.symm
  have hgTwo : g₂ = 1 := by
    have hconj : g * g₂ * g⁻¹ = 1 := by simpa [haone] using ha
    calc
      g₂ = g⁻¹ * (g * g₂ * g⁻¹) * g := by group
      _ = 1 := by rw [hconj]; group
  let retractFour : Delta →* CyclicFour :=
    Monoid.Coprod.lift 1 (MonoidHom.id CyclicFour)
  have hretract := congrArg retractFour hgTwo
  have h10 : (1 : ZMod 4) = 0 := by
    simpa [retractFour, SphereSixComplex.TriangleGroup.g₂.eq_def] using hretract
  have hval := congrArg ZMod.val h10
  exact Nat.one_ne_zero hval

public theorem fuchsianOne_orbit_ne_two (g : Delta) :
    fuchsianSourceAction g • fuchsianOneFixedPoint ≠ fuchsianTwoFixedPoint := by
  intro hg
  have hinv : fuchsianSourceAction g⁻¹ • fuchsianTwoFixedPoint =
      fuchsianOneFixedPoint := by
    calc
      fuchsianSourceAction g⁻¹ • fuchsianTwoFixedPoint =
          fuchsianSourceAction g⁻¹ •
            (fuchsianSourceAction g • fuchsianOneFixedPoint) := congrArg _ hg.symm
      _ = fuchsianOneFixedPoint := by rw [map_inv, inv_smul_smul]
  exact fuchsianTwo_orbit_ne_one g⁻¹ hinv

public theorem ellipticFixedPoints_eq_of_fuchsian
    (hsource : U.sourceAction = fuchsianSourceAction) :
    U.zOne = fuchsianOneFixedPoint ∧ U.zTwo = fuchsianTwoFixedPoint := by
  constructor
  · apply (FreeProductTorsion.fuchsianSourceAction_gOne_fixed_iff U.zOne).mp
    simpa only [← hsource] using U.zOne_fixed
  · apply (FreeProductTorsion.fuchsianSourceAction_gTwo_fixed_iff U.zTwo).mp
    simpa only [← hsource] using U.zTwo_fixed

/-! The two local collars have the same source-side input.  Keeping the varying data in this
record makes the order-specific declarations below aliases, rather than parallel propositions. -/

/-- Indexed data for one elliptic linear collar. -/
public structure IndexedLinearCollarModel (m : ℕ) [NeZero m] where
  center : UpperHalfPlane
  other : UpperHalfPlane
  cayley : UpperHalfPlane → ComplexUnitDisc
  cayley_eq : ∀ z, cayley z = cayleyHomeomorph center z
  cyclicInclusion : FiniteCyclic m → Delta

/-- Source regularity and separation data for an indexed elliptic linear collar. -/
@[expose] public def LinearCollarSourceData
    (m : ℕ) [NeZero m] (M : IndexedLinearCollarModel m) (r : ℝ) : Prop :=
  (∀ z : UpperHalfPlane,
      0 < ‖(M.cayley z : ℂ)‖ →
      ‖(M.cayley z : ℂ)‖ < r →
      IsRegularBasePoint (U := U) z) ∧
    ∀ z x : UpperHalfPlane,
      ‖(M.cayley z : ℂ)‖ < r →
      ‖(M.cayley x : ℂ)‖ < r →
      ∀ g : Delta, U.sourceAction g • x = z →
        ∃ a : FiniteCyclic m, g = M.cyclicInclusion a

public theorem linearCollarSourceData_mono
    (m : ℕ) [NeZero m] {M : IndexedLinearCollarModel m} {r' r : ℝ} (hrr : r' ≤ r)
    (D : LinearCollarSourceData (U := U) m M r) :
    LinearCollarSourceData (U := U) m M r' := by
  rw [LinearCollarSourceData.eq_def] at D ⊢
  constructor
  · intro z hz hzr
    exact D.1 z hz (hzr.trans_le hrr)
  · intro z x hzr hxr g hg
    exact D.2 z x (hzr.trans_le hrr) (hxr.trans_le hrr) g hg

public theorem exists_indexedCollarSlice_radius
    {m : ℕ} [NeZero m] {M : IndexedLinearCollarModel m}
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hcenterOther : M.center ∉ sourceOrbitSet (U := U) M.other) :
    let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
    ∃ S : Set UpperHalfPlane, IsOpen S ∧ M.center ∈ S ∧
      (∀ g : Delta, ((fun y : UpperHalfPlane => g • y) '' S ∩ S).Nonempty ↔
        g ∈ MulAction.stabilizer Delta M.center) ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (∀ z : UpperHalfPlane, ‖(M.cayley z : ℂ)‖ < r →
          z ∈ S ∩ (sourceOrbitSet (U := U) M.other)ᶜ) := by
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianProperlyDiscontinuous_of_source hsource hproper
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g => (fuchsianSourceAction_contMDiff g 0).continuous⟩
  obtain ⟨S, hSopen, hcenterS, _hSinvariant, htranslate⟩ :=
    exists_open_stabilizer_slice (G := Delta) M.center
  let T := S ∩ (sourceOrbitSet (U := U) M.other)ᶜ
  have hTopen : IsOpen T := hSopen.inter
    (sourceOrbitSet_isClosed hproper M.other).isOpen_compl
  have hcenterT : M.center ∈ T := ⟨hcenterS, hcenterOther⟩
  obtain ⟨r, hr, hr1, hrT⟩ :=
    exists_cayleyRadius_subset M.center hTopen hcenterT
  exact ⟨S, hSopen, hcenterS, htranslate, r, hr, hr1, fun z hz =>
    ⟨(hrT z (by simpa [M.cayley_eq z] using hz)).1, (hrT z
      (by simpa [M.cayley_eq z] using hz)).2⟩⟩

/-- The order-three Cayley coordinate and its inclusion into the deck group. -/
public abbrev orderThreeLinearCollarModel :
  IndexedLinearCollarModel 3 :=
  { center := fuchsianOneFixedPoint
    other := fuchsianTwoFixedPoint
    cayley := orderThreeCayleyHomeomorph
    cayley_eq := by intro z; rfl
    cyclicInclusion := Monoid.Coprod.inl }

/-- The order-four Cayley coordinate and its inclusion into the deck group. -/
public abbrev orderFourLinearCollarModel :
  IndexedLinearCollarModel 4 :=
  { center := fuchsianTwoFixedPoint
    other := fuchsianOneFixedPoint
    cayley := orderFourCayleyHomeomorph
    cayley_eq := by intro z; rfl
    cyclicInclusion := Monoid.Coprod.inr }

@[expose] public def OrderThreeLinearCollarSourceData (r : ℝ) : Prop :=
  LinearCollarSourceData (U := U) 3 orderThreeLinearCollarModel r

@[expose] public def OrderFourLinearCollarSourceData (r : ℝ) : Prop :=
  LinearCollarSourceData (U := U) 4 orderFourLinearCollarModel r

public theorem exists_orderThreeLinearCollarSourceData
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ OrderThreeLinearCollarSourceData (U := U) r := by
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianProperlyDiscontinuous_of_source hsource hproper
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g => (fuchsianSourceAction_contMDiff g 0).continuous⟩
  obtain ⟨hzOne, hzTwo⟩ := ellipticFixedPoints_eq_of_fuchsian hsource
  have hcenterNotTwo : fuchsianOneFixedPoint ∉ sourceOrbitSet (U := U) U.zTwo := by
    simp only [sourceOrbitSet.eq_def, mem_iUnion, mem_singleton_iff]
    rintro ⟨g, hg⟩
    apply fuchsianTwo_orbit_ne_one g
    simpa only [hsource, hzOne, hzTwo] using hg.symm
  obtain ⟨S, hSopen, hcenterS, htranslate, r, hr, hr1, hrT⟩ :=
    exists_indexedCollarSlice_radius hsource hproper
      (M := orderThreeLinearCollarModel)
      (by simpa [orderThreeLinearCollarModel, hzTwo] using hcenterNotTwo)
  let T := S ∩ (sourceOrbitSet (U := U) U.zTwo)ᶜ
  refine ⟨r, hr, hr1, ?_⟩
  rw [OrderThreeLinearCollarSourceData.eq_def]
  constructor
  · intro z hzpos hzr
    unfold IsRegularBasePoint
    intro g
    have hzT : z ∈ T := by
      simpa [T, orderThreeLinearCollarModel, hzTwo] using hrT z hzr
    constructor
    · intro hgone
      have hzEq : fuchsianSourceAction g⁻¹ • fuchsianOneFixedPoint = z := by
        calc
          fuchsianSourceAction g⁻¹ • fuchsianOneFixedPoint =
              fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • z) :=
            congrArg _ (by simpa only [hsource, hzOne] using hgone.symm)
          _ = z := by rw [map_inv, inv_smul_smul]
      have hinter : ((fun y : UpperHalfPlane => g⁻¹ • y) '' S ∩ S).Nonempty :=
        ⟨z, ⟨fuchsianOneFixedPoint, hcenterS, by simpa only [hzEq]⟩, hzT.1⟩
      have hfix := (htranslate g⁻¹).mp hinter
      have hzcenter : z = fuchsianOneFixedPoint := by
        rw [← hzEq]
        exact hfix
      rw [hzcenter] at hzpos
      change 0 < ‖(orderThreeCayleyHomeomorph fuchsianOneFixedPoint : ℂ)‖ at hzpos
      rw [orderThreeCayleyHomeomorph.eq_def] at hzpos
      have hc : cayleyHomeomorph fuchsianOneFixedPoint fuchsianOneFixedPoint =
          discCenter := by
        apply Subtype.ext
        simp [cayleyHomeomorph, cayleyDiscCoordinate, cayleyCoordinate, discCenter]
      rw [hc] at hzpos
      norm_num [discCenter] at hzpos
    · intro hgtwo
      have hzOrbit : z ∈ sourceOrbitSet (U := U) U.zTwo := by
        simp only [sourceOrbitSet.eq_def, mem_iUnion, mem_singleton_iff]
        refine ⟨g⁻¹, ?_⟩
        calc
          z = U.sourceAction 1 • z := by rw [map_one, one_smul]
          _ = U.sourceAction (g⁻¹ * g) • z := by rw [inv_mul_cancel]
          _ = U.sourceAction g⁻¹ • (U.sourceAction g • z) := by
            rw [map_mul, mul_smul]
          _ = U.sourceAction g⁻¹ • U.zTwo := congrArg _ hgtwo
      exact hzT.2 hzOrbit
  · intro z x hzr hxr g hg
    have hzS : z ∈ S := (hrT z hzr).1
    have hxS : x ∈ S := (hrT x hxr).1
    have hinter : ((fun y : UpperHalfPlane => g • y) '' S ∩ S).Nonempty :=
      ⟨z, ⟨x, hxS, by
        change fuchsianSourceAction g • x = z
        simpa only [hsource] using hg⟩, hzS⟩
    have hfix := (htranslate g).mp hinter
    change fuchsianSourceAction g • fuchsianOneFixedPoint = fuchsianOneFixedPoint at hfix
    exact establishedFuchsianOneStabilizerExact g |>.mp hfix

public theorem exists_orderFourLinearCollarSourceData
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ OrderFourLinearCollarSourceData (U := U) r := by
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianProperlyDiscontinuous_of_source hsource hproper
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g => (fuchsianSourceAction_contMDiff g 0).continuous⟩
  obtain ⟨hzOne, hzTwo⟩ := ellipticFixedPoints_eq_of_fuchsian hsource
  have hcenterNotOne : fuchsianTwoFixedPoint ∉ sourceOrbitSet (U := U) U.zOne := by
    simp only [sourceOrbitSet.eq_def, mem_iUnion, mem_singleton_iff]
    rintro ⟨g, hg⟩
    apply fuchsianOne_orbit_ne_two g
    simpa only [hsource, hzOne, hzTwo] using hg.symm
  obtain ⟨S, hSopen, hcenterS, htranslate, r, hr, hr1, hrT⟩ :=
    exists_indexedCollarSlice_radius hsource hproper
      (M := orderFourLinearCollarModel)
      (by simpa [orderFourLinearCollarModel, hzOne] using hcenterNotOne)
  let T := S ∩ (sourceOrbitSet (U := U) U.zOne)ᶜ
  refine ⟨r, hr, hr1, ?_⟩
  rw [OrderFourLinearCollarSourceData.eq_def]
  constructor
  · intro z hzpos hzr
    unfold IsRegularBasePoint
    intro g
    have hzT : z ∈ T := by
      simpa [T, orderFourLinearCollarModel, hzOne] using hrT z hzr
    constructor
    · intro hgone
      have hzOrbit : z ∈ sourceOrbitSet (U := U) U.zOne := by
        simp only [sourceOrbitSet.eq_def, mem_iUnion, mem_singleton_iff]
        refine ⟨g⁻¹, ?_⟩
        calc
          z = U.sourceAction 1 • z := by rw [map_one, one_smul]
          _ = U.sourceAction (g⁻¹ * g) • z := by rw [inv_mul_cancel]
          _ = U.sourceAction g⁻¹ • (U.sourceAction g • z) := by
            rw [map_mul, mul_smul]
          _ = U.sourceAction g⁻¹ • U.zOne := congrArg _ hgone
      exact hzT.2 hzOrbit
    · intro hgtwo
      have hzEq : fuchsianSourceAction g⁻¹ • fuchsianTwoFixedPoint = z := by
        calc
          fuchsianSourceAction g⁻¹ • fuchsianTwoFixedPoint =
              fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • z) :=
            congrArg _ (by simpa only [hsource, hzTwo] using hgtwo.symm)
          _ = z := by rw [map_inv, inv_smul_smul]
      have hinter : ((fun y : UpperHalfPlane => g⁻¹ • y) '' S ∩ S).Nonempty :=
        ⟨z, ⟨fuchsianTwoFixedPoint, hcenterS, by simpa only [hzEq]⟩, hzT.1⟩
      have hfix := (htranslate g⁻¹).mp hinter
      have hzcenter : z = fuchsianTwoFixedPoint := by
        rw [← hzEq]
        exact hfix
      rw [hzcenter] at hzpos
      change 0 < ‖(orderFourCayleyHomeomorph fuchsianTwoFixedPoint : ℂ)‖ at hzpos
      rw [orderFourCayleyHomeomorph.eq_def] at hzpos
      have hc : cayleyHomeomorph fuchsianTwoFixedPoint fuchsianTwoFixedPoint =
          discCenter := by
        apply Subtype.ext
        simp [cayleyHomeomorph, cayleyDiscCoordinate, cayleyCoordinate, discCenter]
      rw [hc] at hzpos
      norm_num [discCenter] at hzpos
  · intro z x hzr hxr g hg
    have hzS : z ∈ S := (hrT z hzr).1
    have hxS : x ∈ S := (hrT x hxr).1
    have hinter : ((fun y : UpperHalfPlane => g • y) '' S ∩ S).Nonempty :=
      ⟨z, ⟨x, hxS, by
        change fuchsianSourceAction g • x = z
        simpa only [hsource] using hg⟩, hzS⟩
    have hfix := (htranslate g).mp hinter
    change fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint at hfix
    exact establishedFuchsianTwoStabilizerExact g |>.mp hfix

@[expose] public noncomputable def orderThreeCollarToRegularPart
    (D : OrderThreeLinearCollarSourceData (U := U) r) :
    orderThreePuncturedFamilyCollar F r →
      {q : TotalSpace (parameterMap F) |
        IsRegularBasePoint (U := U) (familyTotalSpaceBase F q)} :=
  fun q => ⟨q, by
    rw [OrderThreeLinearCollarSourceData.eq_def] at D
    apply D.1 (familyTotalSpaceBase F q)
    · simpa only [orderThreePuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
        orderThreeFamilyRadius.eq_def] using q.property.1
    · simpa only [orderThreePuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
        orderThreeFamilyRadius.eq_def] using q.property.2⟩

@[expose] public noncomputable def orderFourCollarToRegularPart
    (D : OrderFourLinearCollarSourceData (U := U) r) :
    orderFourPuncturedFamilyCollar F r →
      {q : TotalSpace (parameterMap F) |
        IsRegularBasePoint (U := U) (familyTotalSpaceBase F q)} :=
  fun q => ⟨q, by
    rw [OrderFourLinearCollarSourceData.eq_def] at D
    apply D.1 (familyTotalSpaceBase F q)
    · simpa only [orderFourPuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
        orderFourFamilyRadius.eq_def] using q.property.1
    · simpa only [orderFourPuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
        orderFourFamilyRadius.eq_def] using q.property.2⟩

@[expose] public noncomputable def orderThreeCollarToRegular
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (D : OrderThreeLinearCollarSourceData (U := U) r) :
    orderThreePuncturedFamilyCollar F r → RegularTotalSpace F :=
  (regularFamilyPartHomeomorph F hproper).symm ∘ orderThreeCollarToRegularPart F D

@[expose] public noncomputable def orderFourCollarToRegular
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (D : OrderFourLinearCollarSourceData (U := U) r) :
    orderFourPuncturedFamilyCollar F r → RegularTotalSpace F :=
  (regularFamilyPartHomeomorph F hproper).symm ∘ orderFourCollarToRegularPart F D

public theorem regularFamilyInclusion_orderThreeCollarToRegular
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (D : OrderThreeLinearCollarSourceData (U := U) r)
    (q : orderThreePuncturedFamilyCollar F r) :
    regularFamilyInclusion F (orderThreeCollarToRegular F hproper D q) = q := by
  have h := (regularFamilyPartHomeomorph F hproper).apply_symm_apply
    (orderThreeCollarToRegularPart F D q)
  exact congrArg Subtype.val h

public theorem regularFamilyInclusion_orderFourCollarToRegular
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (D : OrderFourLinearCollarSourceData (U := U) r)
    (q : orderFourPuncturedFamilyCollar F r) :
    regularFamilyInclusion F (orderFourCollarToRegular F hproper D q) = q := by
  have h := (regularFamilyPartHomeomorph F hproper).apply_symm_apply
    (orderFourCollarToRegularPart F D q)
  exact congrArg Subtype.val h

public theorem orderThreeCollarToRegularPart_isOpenEmbedding
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (D : OrderThreeLinearCollarSourceData (U := U) r) :
    IsOpenEmbedding (orderThreeCollarToRegularPart F D) := by
  have hregularOpen : IsOpen
      {q : TotalSpace (parameterMap F) |
        IsRegularBasePoint (U := U) (familyTotalSpaceBase F q)} :=
    (isOpen_isRegularBasePoint hproper).preimage (familyTotalSpaceBase_continuous F)
  apply (IsOpenEmbedding.of_comp_iff (orderThreeCollarToRegularPart F D)
    hregularOpen.isOpenEmbedding_subtypeVal).mp
  have heq : Subtype.val ∘ orderThreeCollarToRegularPart F D = Subtype.val := by
    funext q
    rfl
  rw [heq]
  exact (orderThreePuncturedFamilyCollar_isOpen F r).isOpenEmbedding_subtypeVal

public theorem orderFourCollarToRegularPart_isOpenEmbedding
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (D : OrderFourLinearCollarSourceData (U := U) r) :
    IsOpenEmbedding (orderFourCollarToRegularPart F D) := by
  have hregularOpen : IsOpen
      {q : TotalSpace (parameterMap F) |
        IsRegularBasePoint (U := U) (familyTotalSpaceBase F q)} :=
    (isOpen_isRegularBasePoint hproper).preimage (familyTotalSpaceBase_continuous F)
  apply (IsOpenEmbedding.of_comp_iff (orderFourCollarToRegularPart F D)
    hregularOpen.isOpenEmbedding_subtypeVal).mp
  have heq : Subtype.val ∘ orderFourCollarToRegularPart F D = Subtype.val := by
    funext q
    rfl
  rw [heq]
  exact (orderFourPuncturedFamilyCollar_isOpen F r).isOpenEmbedding_subtypeVal

public theorem orderThreeCollarToRegular_isOpenEmbedding
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (D : OrderThreeLinearCollarSourceData (U := U) r) :
    IsOpenEmbedding (orderThreeCollarToRegular F hproper D) :=
  (regularFamilyPartHomeomorph F hproper).symm.isOpenEmbedding.comp
    (orderThreeCollarToRegularPart_isOpenEmbedding F hproper D)

public theorem orderFourCollarToRegular_isOpenEmbedding
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (D : OrderFourLinearCollarSourceData (U := U) r) :
    IsOpenEmbedding (orderFourCollarToRegular F hproper D) :=
  (regularFamilyPartHomeomorph F hproper).symm.isOpenEmbedding.comp
    (orderFourCollarToRegularPart_isOpenEmbedding F hproper D)

public theorem orderThreeLinear_actionMap
    (a : FiniteCyclic 3) (q : TotalSpace (parameterMap F)) :
    actionMap (orderThreeLinearFamilyAction F) a q =
      familyDeckMap F (Monoid.Coprod.inl a) q :=
  rfl

public theorem orderFourLinear_actionMap
    (a : FiniteCyclic 4) (q : TotalSpace (parameterMap F)) :
    actionMap (orderFourLinearFamilyAction F) a q =
      familyDeckMap F (Monoid.Coprod.inr a) q :=
  rfl

public theorem orderThreeCollarToRegular_action
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderThreeLinearCollarSourceData (U := U) r)
    (a : FiniteCyclic 3) (q : (orderThreeLinearPuncturedCarrier F hsource r).carrier) :
    orderThreeCollarToRegular F hproper D
        (restrictedActionMap (orderThreeLinearPuncturedCarrier F hsource r) a q) =
      regularFamilyDeckMap F (Monoid.Coprod.inl a)
        (orderThreeCollarToRegular F hproper D q) := by
  change orderThreePuncturedFamilyCollar F r at q
  apply regularFamilyInclusion_injective F
  calc
    regularFamilyInclusion F (orderThreeCollarToRegular F hproper D
        (restrictedActionMap (orderThreeLinearPuncturedCarrier F hsource r) a q)) =
        (restrictedActionMap (orderThreeLinearPuncturedCarrier F hsource r) a q).1 :=
      regularFamilyInclusion_orderThreeCollarToRegular F hproper D _
    _ = actionMap (orderThreeLinearFamilyAction F) a q := rfl
    _ = familyDeckMap F (Monoid.Coprod.inl a) q := orderThreeLinear_actionMap F a q
    _ = familyDeckMap F (Monoid.Coprod.inl a)
        (regularFamilyInclusion F (orderThreeCollarToRegular F hproper D q)) :=
      congrArg _ (regularFamilyInclusion_orderThreeCollarToRegular F hproper D q).symm
    _ = regularFamilyInclusion F (regularFamilyDeckMap F (Monoid.Coprod.inl a)
        (orderThreeCollarToRegular F hproper D q)) :=
      (regularFamilyInclusion_regularFamilyDeckMap F _ _).symm

public theorem orderFourCollarToRegular_action
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderFourLinearCollarSourceData (U := U) r)
    (a : FiniteCyclic 4) (q : (orderFourLinearPuncturedCarrier F hsource r).carrier) :
    orderFourCollarToRegular F hproper D
        (restrictedActionMap (orderFourLinearPuncturedCarrier F hsource r) a q) =
      regularFamilyDeckMap F (Monoid.Coprod.inr a)
        (orderFourCollarToRegular F hproper D q) := by
  change orderFourPuncturedFamilyCollar F r at q
  apply regularFamilyInclusion_injective F
  calc
    regularFamilyInclusion F (orderFourCollarToRegular F hproper D
        (restrictedActionMap (orderFourLinearPuncturedCarrier F hsource r) a q)) =
        (restrictedActionMap (orderFourLinearPuncturedCarrier F hsource r) a q).1 :=
      regularFamilyInclusion_orderFourCollarToRegular F hproper D _
    _ = actionMap (orderFourLinearFamilyAction F) a q := rfl
    _ = familyDeckMap F (Monoid.Coprod.inr a) q := orderFourLinear_actionMap F a q
    _ = familyDeckMap F (Monoid.Coprod.inr a)
        (regularFamilyInclusion F (orderFourCollarToRegular F hproper D q)) :=
      congrArg _ (regularFamilyInclusion_orderFourCollarToRegular F hproper D q).symm
    _ = regularFamilyInclusion F (regularFamilyDeckMap F (Monoid.Coprod.inr a)
        (orderFourCollarToRegular F hproper D q)) :=
      (regularFamilyInclusion_regularFamilyDeckMap F _ _).symm

/-- The restricted order-three linear collar maps canonically to the paper's punctured global
family quotient. -/
@[expose] public noncomputable def orderThreeLinearCollarToPuncturedGlobalFamily
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderThreeLinearCollarSourceData (U := U) r) :
    Quotient (restrictedOrbitRel (orderThreeLinearFamilyAction F)
      (orderThreeLinearPuncturedCarrier F hsource r)) → PuncturedGlobalFamily F := by
  let _ := orderThreeLinearFamilyAction F
  let _ := regularFamilyDeckAction F
  refine Quotient.map (orderThreeCollarToRegular F hproper D) ?_
  intro q x hqx
  let _ := restrictedMulAction (orderThreeLinearFamilyAction F)
    (orderThreeLinearPuncturedCarrier F hsource r)
  change MulAction.orbitRel (FiniteCyclic 3) _ q x at hqx
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hqx
  change MulAction.orbitRel Delta _
    (orderThreeCollarToRegular F hproper D q)
    (orderThreeCollarToRegular F hproper D x)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  obtain ⟨a, ha⟩ := hqx
  refine ⟨Monoid.Coprod.inl a, ?_⟩
  change regularFamilyDeckMap F (Monoid.Coprod.inl a)
    (orderThreeCollarToRegular F hproper D x) =
      orderThreeCollarToRegular F hproper D q
  exact (orderThreeCollarToRegular_action F hproper hsource D a x).symm.trans
    (congrArg (orderThreeCollarToRegular F hproper D) ha)

/-- The restricted order-four linear collar maps canonically to the paper's punctured global
family quotient. -/
@[expose] public noncomputable def orderFourLinearCollarToPuncturedGlobalFamily
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderFourLinearCollarSourceData (U := U) r) :
    Quotient (restrictedOrbitRel (orderFourLinearFamilyAction F)
      (orderFourLinearPuncturedCarrier F hsource r)) → PuncturedGlobalFamily F := by
  let _ := orderFourLinearFamilyAction F
  let _ := regularFamilyDeckAction F
  refine Quotient.map (orderFourCollarToRegular F hproper D) ?_
  intro q x hqx
  let _ := restrictedMulAction (orderFourLinearFamilyAction F)
    (orderFourLinearPuncturedCarrier F hsource r)
  change MulAction.orbitRel (FiniteCyclic 4) _ q x at hqx
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hqx
  change MulAction.orbitRel Delta _
    (orderFourCollarToRegular F hproper D q)
    (orderFourCollarToRegular F hproper D x)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  obtain ⟨a, ha⟩ := hqx
  refine ⟨Monoid.Coprod.inr a, ?_⟩
  change regularFamilyDeckMap F (Monoid.Coprod.inr a)
    (orderFourCollarToRegular F hproper D x) =
      orderFourCollarToRegular F hproper D q
  exact (orderFourCollarToRegular_action F hproper hsource D a x).symm.trans
    (congrArg (orderFourCollarToRegular F hproper D) ha)

@[simp]
public theorem orderThreeLinearCollarToPuncturedGlobalFamily_mk
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderThreeLinearCollarSourceData (U := U) r)
    (q : (orderThreeLinearPuncturedCarrier F hsource r).carrier) :
    orderThreeLinearCollarToPuncturedGlobalFamily F hproper hsource D (Quotient.mk _ q) =
      Quotient.mk _ (orderThreeCollarToRegular F hproper D q) :=
  rfl

@[simp]
public theorem orderFourLinearCollarToPuncturedGlobalFamily_mk
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderFourLinearCollarSourceData (U := U) r)
    (q : (orderFourLinearPuncturedCarrier F hsource r).carrier) :
    orderFourLinearCollarToPuncturedGlobalFamily F hproper hsource D (Quotient.mk _ q) =
      Quotient.mk _ (orderFourCollarToRegular F hproper D q) :=
  rfl

public theorem orderThreeLinearCollarToPuncturedGlobalFamily_injective
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderThreeLinearCollarSourceData (U := U) r) :
    Function.Injective (orderThreeLinearCollarToPuncturedGlobalFamily F hproper hsource D) := by
  let _ := orderThreeLinearFamilyAction F
  intro Q R hQR
  induction Q using Quotient.inductionOn with
  | _ q =>
    induction R using Quotient.inductionOn with
    | _ x =>
      let _ := regularFamilyDeckAction F
      rw [orderThreeLinearCollarToPuncturedGlobalFamily_mk,
        orderThreeLinearCollarToPuncturedGlobalFamily_mk] at hQR
      rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hQR
      obtain ⟨g, hg⟩ := hQR
      change regularFamilyDeckMap F g (orderThreeCollarToRegular F hproper D x) =
        orderThreeCollarToRegular F hproper D q at hg
      have htotal : familyDeckMap F g x = q := by
        calc
          familyDeckMap F g x = familyDeckMap F g
              (regularFamilyInclusion F (orderThreeCollarToRegular F hproper D x)) :=
            congrArg _ (regularFamilyInclusion_orderThreeCollarToRegular F hproper D x).symm
          _ = regularFamilyInclusion F
              (regularFamilyDeckMap F g (orderThreeCollarToRegular F hproper D x)) :=
            (regularFamilyInclusion_regularFamilyDeckMap F g _).symm
          _ = regularFamilyInclusion F (orderThreeCollarToRegular F hproper D q) :=
            congrArg _ hg
          _ = q := regularFamilyInclusion_orderThreeCollarToRegular F hproper D q
      have hbase := congrArg (familyTotalSpaceBase F) htotal
      rw [familyTotalSpaceBase_familyDeckMap] at hbase
      rw [OrderThreeLinearCollarSourceData.eq_def] at D
      obtain ⟨a, ha⟩ := D.2 (familyTotalSpaceBase F q) (familyTotalSpaceBase F x)
        (by simpa [orderThreeLinearCollarModel, orderThreePuncturedFamilyCollar.eq_def,
          Set.mem_ofPred_eq, orderThreeFamilyRadius.eq_def] using q.property.2)
        (by simpa [orderThreeLinearCollarModel, orderThreePuncturedFamilyCollar.eq_def,
          Set.mem_ofPred_eq, orderThreeFamilyRadius.eq_def] using x.property.2) g hbase
      apply Quotient.sound
      let _ := restrictedMulAction (orderThreeLinearFamilyAction F)
        (orderThreeLinearPuncturedCarrier F hsource r)
      change MulAction.orbitRel (FiniteCyclic 3) _ q x
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change actionMap (orderThreeLinearFamilyAction F) a x = q
      have ha' : g = Monoid.Coprod.inl a := by
        simpa [orderThreeLinearCollarModel] using ha
      rw [orderThreeLinear_actionMap, ← ha']
      exact htotal

public theorem orderFourLinearCollarToPuncturedGlobalFamily_injective
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderFourLinearCollarSourceData (U := U) r) :
    Function.Injective (orderFourLinearCollarToPuncturedGlobalFamily F hproper hsource D) := by
  let _ := orderFourLinearFamilyAction F
  intro Q R hQR
  induction Q using Quotient.inductionOn with
  | _ q =>
    induction R using Quotient.inductionOn with
    | _ x =>
      let _ := regularFamilyDeckAction F
      rw [orderFourLinearCollarToPuncturedGlobalFamily_mk,
        orderFourLinearCollarToPuncturedGlobalFamily_mk] at hQR
      rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hQR
      obtain ⟨g, hg⟩ := hQR
      change regularFamilyDeckMap F g (orderFourCollarToRegular F hproper D x) =
        orderFourCollarToRegular F hproper D q at hg
      have htotal : familyDeckMap F g x = q := by
        calc
          familyDeckMap F g x = familyDeckMap F g
              (regularFamilyInclusion F (orderFourCollarToRegular F hproper D x)) :=
            congrArg _ (regularFamilyInclusion_orderFourCollarToRegular F hproper D x).symm
          _ = regularFamilyInclusion F
              (regularFamilyDeckMap F g (orderFourCollarToRegular F hproper D x)) :=
            (regularFamilyInclusion_regularFamilyDeckMap F g _).symm
          _ = regularFamilyInclusion F (orderFourCollarToRegular F hproper D q) :=
            congrArg _ hg
          _ = q := regularFamilyInclusion_orderFourCollarToRegular F hproper D q
      have hbase := congrArg (familyTotalSpaceBase F) htotal
      rw [familyTotalSpaceBase_familyDeckMap] at hbase
      rw [OrderFourLinearCollarSourceData.eq_def] at D
      obtain ⟨a, ha⟩ := D.2 (familyTotalSpaceBase F q) (familyTotalSpaceBase F x)
        (by simpa [orderFourLinearCollarModel, orderFourPuncturedFamilyCollar.eq_def,
          Set.mem_ofPred_eq, orderFourFamilyRadius.eq_def] using q.property.2)
        (by simpa [orderFourLinearCollarModel, orderFourPuncturedFamilyCollar.eq_def,
          Set.mem_ofPred_eq, orderFourFamilyRadius.eq_def] using x.property.2) g hbase
      apply Quotient.sound
      let _ := restrictedMulAction (orderFourLinearFamilyAction F)
        (orderFourLinearPuncturedCarrier F hsource r)
      change MulAction.orbitRel (FiniteCyclic 4) _ q x
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change actionMap (orderFourLinearFamilyAction F) a x = q
      have ha' : g = Monoid.Coprod.inr a := by
        simpa [orderFourLinearCollarModel] using ha
      rw [orderFourLinear_actionMap, ← ha']
      exact htotal

public theorem orderThreeLinearCollarToPuncturedGlobalFamily_continuous
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderThreeLinearCollarSourceData (U := U) r) :
    Continuous (orderThreeLinearCollarToPuncturedGlobalFamily F hproper hsource D) := by
  change Continuous (Quotient.map (orderThreeCollarToRegular F hproper D) _)
  exact continuous_quot_map _
    (orderThreeCollarToRegular_isOpenEmbedding F hproper D).continuous

public theorem orderFourLinearCollarToPuncturedGlobalFamily_continuous
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderFourLinearCollarSourceData (U := U) r) :
    Continuous (orderFourLinearCollarToPuncturedGlobalFamily F hproper hsource D) := by
  change Continuous (Quotient.map (orderFourCollarToRegular F hproper D) _)
  exact continuous_quot_map _
    (orderFourCollarToRegular_isOpenEmbedding F hproper D).continuous

public theorem orderThreeLinearCollarToPuncturedGlobalFamily_isOpenMap
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderThreeLinearCollarSourceData (U := U) r)
    (hcontinuous : letI := regularFamilyDeckAction F;
      ContinuousConstSMul Delta (RegularTotalSpace F)) :
    IsOpenMap (orderThreeLinearCollarToPuncturedGlobalFamily F hproper hsource D) := by
  let _ := regularFamilyDeckAction F
  let _ : ContinuousConstSMul Delta (RegularTotalSpace F) := hcontinuous
  apply IsOpenMap.of_comp continuous_quot_mk Quotient.mk_surjective
  have hquotient : IsOpenMap
      (quotientProjection : RegularTotalSpace F → PuncturedGlobalFamily F) := by
    let _ : Setoid (RegularTotalSpace F) := MulAction.orbitRel Delta _
    rw [quotientProjection.eq_def]
    change IsOpenMap (Quotient.mk' : RegularTotalSpace F →
      Quotient (MulAction.orbitRel Delta (RegularTotalSpace F)))
    exact isOpenMap_quotient_mk'_mul
  let e : (orderThreeLinearPuncturedCarrier F hsource r).carrier ≃ₜ
      orderThreePuncturedFamilyCollar F r := Homeomorph.setCongr (by
    rw [orderThreeLinearPuncturedCarrier.eq_def])
  have hopen : IsOpenMap
      (quotientProjection ∘ orderThreeCollarToRegular F hproper D ∘ e) :=
    hquotient.comp ((orderThreeCollarToRegular_isOpenEmbedding F hproper D).isOpenMap.comp
      e.isOpenMap)
  convert hopen using 1
  funext q
  exact orderThreeLinearCollarToPuncturedGlobalFamily_mk F hproper hsource D q

public theorem orderFourLinearCollarToPuncturedGlobalFamily_isOpenMap
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderFourLinearCollarSourceData (U := U) r)
    (hcontinuous : letI := regularFamilyDeckAction F;
      ContinuousConstSMul Delta (RegularTotalSpace F)) :
    IsOpenMap (orderFourLinearCollarToPuncturedGlobalFamily F hproper hsource D) := by
  let _ := regularFamilyDeckAction F
  let _ : ContinuousConstSMul Delta (RegularTotalSpace F) := hcontinuous
  apply IsOpenMap.of_comp continuous_quot_mk Quotient.mk_surjective
  have hquotient : IsOpenMap
      (quotientProjection : RegularTotalSpace F → PuncturedGlobalFamily F) := by
    let _ : Setoid (RegularTotalSpace F) := MulAction.orbitRel Delta _
    rw [quotientProjection.eq_def]
    change IsOpenMap (Quotient.mk' : RegularTotalSpace F →
      Quotient (MulAction.orbitRel Delta (RegularTotalSpace F)))
    exact isOpenMap_quotient_mk'_mul
  let e : (orderFourLinearPuncturedCarrier F hsource r).carrier ≃ₜ
      orderFourPuncturedFamilyCollar F r := Homeomorph.setCongr (by
    rw [orderFourLinearPuncturedCarrier.eq_def])
  have hopen : IsOpenMap
      (quotientProjection ∘ orderFourCollarToRegular F hproper D ∘ e) :=
    hquotient.comp ((orderFourCollarToRegular_isOpenEmbedding F hproper D).isOpenMap.comp
      e.isOpenMap)
  convert hopen using 1
  funext q
  exact orderFourLinearCollarToPuncturedGlobalFamily_mk F hproper hsource D q

public theorem orderThreeLinearCollarToPuncturedGlobalFamily_isOpenEmbedding
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderThreeLinearCollarSourceData (U := U) r)
    (hcontinuous : letI := regularFamilyDeckAction F;
      ContinuousConstSMul Delta (RegularTotalSpace F)) :
    IsOpenEmbedding
      (orderThreeLinearCollarToPuncturedGlobalFamily F hproper hsource D) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (orderThreeLinearCollarToPuncturedGlobalFamily_continuous F hproper hsource D)
    (orderThreeLinearCollarToPuncturedGlobalFamily_injective F hproper hsource D)
    (orderThreeLinearCollarToPuncturedGlobalFamily_isOpenMap F hproper hsource D hcontinuous)

public theorem orderFourLinearCollarToPuncturedGlobalFamily_isOpenEmbedding
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderFourLinearCollarSourceData (U := U) r)
    (hcontinuous : letI := regularFamilyDeckAction F;
      ContinuousConstSMul Delta (RegularTotalSpace F)) :
    IsOpenEmbedding
      (orderFourLinearCollarToPuncturedGlobalFamily F hproper hsource D) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (orderFourLinearCollarToPuncturedGlobalFamily_continuous F hproper hsource D)
    (orderFourLinearCollarToPuncturedGlobalFamily_injective F hproper hsource D)
    (orderFourLinearCollarToPuncturedGlobalFamily_isOpenMap F hproper hsource D hcontinuous)

/-- The logarithmically gauged order-three affine collar embeds as an open subset of the
paper's punctured global family. -/
@[expose] public noncomputable def orderThreeAffineCollarToPuncturedGlobalFamily
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderThreeLinearCollarSourceData (U := U) r) :
    Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction F)
      (orderThreeAffinePuncturedCarrier F hsource r)) → PuncturedGlobalFamily F :=
  orderThreeLinearCollarToPuncturedGlobalFamily F hproper hsource D ∘
    orderThreePuncturedCollarQuotientHomeomorph F hprojection hsource r

/-- The logarithmically gauged order-four affine collar embeds as an open subset of the
paper's punctured global family. -/
@[expose] public noncomputable def orderFourAffineCollarToPuncturedGlobalFamily
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderFourLinearCollarSourceData (U := U) r) :
    Quotient (restrictedOrbitRel (orderFourAffineFamilyAction F)
      (orderFourAffinePuncturedCarrier F hsource r)) → PuncturedGlobalFamily F :=
  orderFourLinearCollarToPuncturedGlobalFamily F hproper hsource D ∘
    orderFourPuncturedCollarQuotientHomeomorph F hprojection hsource r

public theorem orderThreeAffineCollarToPuncturedGlobalFamily_isOpenEmbedding
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderThreeLinearCollarSourceData (U := U) r)
    (hcontinuous : letI := regularFamilyDeckAction F;
      ContinuousConstSMul Delta (RegularTotalSpace F)) :
    IsOpenEmbedding
      (orderThreeAffineCollarToPuncturedGlobalFamily F hprojection hproper hsource D) :=
  (orderThreeLinearCollarToPuncturedGlobalFamily_isOpenEmbedding
    F hproper hsource D hcontinuous).comp
      (orderThreePuncturedCollarQuotientHomeomorph F hprojection hsource r).isOpenEmbedding

public theorem orderFourAffineCollarToPuncturedGlobalFamily_isOpenEmbedding
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderFourLinearCollarSourceData (U := U) r)
    (hcontinuous : letI := regularFamilyDeckAction F;
      ContinuousConstSMul Delta (RegularTotalSpace F)) :
    IsOpenEmbedding
      (orderFourAffineCollarToPuncturedGlobalFamily F hprojection hproper hsource D) :=
  (orderFourLinearCollarToPuncturedGlobalFamily_isOpenEmbedding
    F hproper hsource D hcontinuous).comp
      (orderFourPuncturedCollarQuotientHomeomorph F hprojection hsource r).isOpenEmbedding

public theorem orderThreeAffineCollarToPuncturedGlobalFamily_isOpenEmbedding_actual
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderThreeLinearCollarSourceData (U := U) r) :
    IsOpenEmbedding
      (orderThreeAffineCollarToPuncturedGlobalFamily F hprojection hproper hsource D) := by
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace (RegularBase (U := U)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := U)) := regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    fun a => (regularPeriodSection_contMDiff F hproper a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
      (regularParameterMap_compactUniformLowerBound F))
  let _ : LocallyCompactSpace (RegularTotalSpace F) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction F
  let hcontinuous : ContinuousConstSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_continuousConstSMul F hproper
  exact orderThreeAffineCollarToPuncturedGlobalFamily_isOpenEmbedding
    F hprojection hproper hsource D hcontinuous

public theorem orderFourAffineCollarToPuncturedGlobalFamily_isOpenEmbedding_actual
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderFourLinearCollarSourceData (U := U) r) :
    IsOpenEmbedding
      (orderFourAffineCollarToPuncturedGlobalFamily F hprojection hproper hsource D) := by
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace (RegularBase (U := U)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := U)) := regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    fun a => (regularPeriodSection_contMDiff F hproper a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
      (regularParameterMap_compactUniformLowerBound F))
  let _ : LocallyCompactSpace (RegularTotalSpace F) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction F
  let hcontinuous : ContinuousConstSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_continuousConstSMul F hproper
  exact orderFourAffineCollarToPuncturedGlobalFamily_isOpenEmbedding
    F hprojection hproper hsource D hcontinuous

public theorem exists_orderThreeAffineCollarOpenEmbedding
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∃ D : OrderThreeLinearCollarSourceData (U := U) r,
        IsOpenEmbedding
          (orderThreeAffineCollarToPuncturedGlobalFamily
            F hprojection hproper hsource D) := by
  obtain ⟨r, hr, hr1, D⟩ := exists_orderThreeLinearCollarSourceData
    (U := U) hsource hproper
  exact ⟨r, hr, hr1, D,
    orderThreeAffineCollarToPuncturedGlobalFamily_isOpenEmbedding_actual
      F hprojection hproper hsource D⟩

public theorem exists_orderFourAffineCollarOpenEmbedding
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∃ D : OrderFourLinearCollarSourceData (U := U) r,
        IsOpenEmbedding
          (orderFourAffineCollarToPuncturedGlobalFamily
            F hprojection hproper hsource D) := by
  obtain ⟨r, hr, hr1, D⟩ := exists_orderFourLinearCollarSourceData
    (U := U) hsource hproper
  exact ⟨r, hr, hr1, D,
    orderFourAffineCollarToPuncturedGlobalFamily_isOpenEmbedding_actual
      F hprojection hproper hsource D⟩

end

end SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
