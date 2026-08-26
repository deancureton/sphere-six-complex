module

public import SphereSixComplex.Geometry.EllipticAnalyticCollarDescent
public import SphereSixComplex.Geometry.EllipticAffineGlobalSeparation
public import SphereSixComplex.Geometry.RegularTorusFamily
import all SphereSixComplex.TriangleGroup.Representation
import all SphereSixComplex.Geometry.GlobalTorusFamily
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Linear elliptic collars inside the punctured global family

The regular varying torus family is the open part of the unexcised varying torus family over
the regular source locus.  This module constructs that open embedding and uses it to compare a
small finite cyclic elliptic collar with the full linear triangle-group quotient.
-/

namespace SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent

open Filter Set Topology
open scoped ContDiff Manifold
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
open SphereSixComplex.Geometry.EllipticAnalyticCollarDescent
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

/-- The inclusion of the regular vector-bundle cover is complex smooth for the inherited
atlas on the open regular base. -/
public theorem regularBundleInclusion_contMDiff
    (hproper : SourceActionProperlyDiscontinuous (U := U)) (n : WithTop ℕ∞) :
    letI := regularBaseChartedSpace hproper
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n
      (regularBundleInclusion (U := U)) := by
  let _ := regularBaseChartedSpace hproper
  have hval : ContMDiff GlobalDeckBaseModel GlobalDeckBaseModel n
      (fun z : RegularBase (U := U) ↦ z.1) := by
    change ContMDiff GlobalDeckBaseModel GlobalDeckBaseModel n
      (Subtype.val : regularBaseOpen hproper → UpperHalfPlane)
    exact contMDiff_subtype_val
  exact (hval.comp contMDiff_fst).prodMk contMDiff_snd

/-- The regular vector-bundle inclusion is locally biholomorphic. -/
public theorem regularBundleInclusion_isLocalDiffeomorph
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := regularBaseChartedSpace hproper
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (regularBundleInclusion (U := U)) := by
  let _ := regularBaseChartedSpace hproper
  intro p
  let hnonempty : Nonempty (regularBaseOpen hproper) := ⟨p.1⟩
  let ebase := (regularBaseOpen hproper).openPartialHomeomorphSubtypeCoe hnonempty
  let efiber := OpenPartialHomeomorph.refl ComplexTwoSpace
  let e := ebase.prod efiber
  let Φ : PartialDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      (RegularBase (U := U) × ComplexTwoSpace)
      (UpperHalfPlane × ComplexTwoSpace) RegularSmoothnessOrder := by
    change PartialDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      ((regularBaseOpen hproper) × ComplexTwoSpace)
      (UpperHalfPlane × ComplexTwoSpace) RegularSmoothnessOrder
    exact
      { toPartialEquiv := e.toPartialEquiv
        open_source := e.open_source
        open_target := e.open_target
        contMDiffOn_toFun := by
          have hsource : e.source = Set.univ := by
            simp [e, ebase, efiber]
          rw [hsource]
          exact (regularBundleInclusion_contMDiff (U := U) hproper
            RegularSmoothnessOrder).contMDiffOn
        contMDiffOn_invFun := by
          intro y hy
          have hbase : ContMDiffWithinAt GlobalDeckTotalModel GlobalDeckBaseModel
              RegularSmoothnessOrder (fun x : UpperHalfPlane × ComplexTwoSpace ↦
                ebase.symm x.1) e.target y := by
            apply (ContMDiffWithinAt.subtypeVal_comp_iff
              (regularBaseOpen hproper) _ e.target y).mp
            apply contMDiff_fst.contMDiffAt.contMDiffWithinAt.congr_of_mem _ hy
            intro x hx
            change ebase (ebase.symm x.1) = x.1
            exact ebase.right_inv hx.1
          have hfiber : ContMDiffWithinAt GlobalDeckTotalModel GlobalDeckFiberModel
              RegularSmoothnessOrder (fun x : UpperHalfPlane × ComplexTwoSpace ↦ x.2)
              e.target y :=
            contMDiff_snd.contMDiffAt.contMDiffWithinAt
          simpa [e, efiber] using hbase.prodMk hfiber }
  have hp : p ∈ Φ.source := by
    change p ∈ e.source
    simp [e, ebase, efiber]
    trivial
  have hΦ := Φ.isLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
    RegularSmoothnessOrder hp
  have heq : (Φ : RegularBase (U := U) × ComplexTwoSpace →
      UpperHalfPlane × ComplexTwoSpace) = regularBundleInclusion := by
    funext q
    rfl
  rw [← heq]
  exact hΦ

/-- Local biholomorphicity is unchanged when two maps agree on a neighbourhood of the point. -/
private theorem isLocalDiffeomorphAt_congr_of_eventuallyEq
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) M]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) N]
    {f g : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder f x) (hfg : f =ᶠ[nhds x] g) :
    IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder g x := by
  rw [IsLocalDiffeomorphAt.eq_def] at hf ⊢
  obtain ⟨Φ, hx, hfΦ⟩ := hf
  obtain ⟨s, hs, hfgs⟩ := hfg.exists_mem
  obtain ⟨t, hts, htopen, hxt⟩ := mem_nhds_iff.mp hs
  let Ψ : PartialDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel M N
      RegularSmoothnessOrder :=
    { toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).toPartialEquiv
      open_source := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).open_source
      open_target := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono inter_subset_left
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono inter_subset_left }
  refine ⟨Ψ, ?_, ?_⟩
  · change x ∈ Φ.source ∩ t
    exact ⟨hx, hxt⟩
  · intro y hy
    change y ∈ Φ.source ∩ t at hy
    calc
      g y = f y := (hfgs (hts hy.2)).symm
      _ = Φ y := hfΦ hy.1
      _ = Ψ y := rfl

/-- Inclusion of an open submanifold into its ambient manifold is locally biholomorphic. -/
private theorem openSubtypeVal_isLocalDiffeomorph
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) M]
    (V : TopologicalSpace.Opens M) :
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (Subtype.val : V → M) := by
  intro p
  let hnonempty : Nonempty V := ⟨p⟩
  let e := V.openPartialHomeomorphSubtypeCoe hnonempty
  let Φ : PartialDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel V M
      RegularSmoothnessOrder :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        apply (ContMDiffWithinAt.subtypeVal_comp_iff V _ e.target y).mp
        apply contMDiffAt_id.contMDiffWithinAt.congr_of_mem _ hy
        intro z hz
        change e (e.symm z) = z
        exact e.right_inv hz }
  have hp : p ∈ Φ.source := by
    change p ∈ e.source
    simp [e]
  have hΦ := Φ.isLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
    RegularSmoothnessOrder hp
  have heq : (Φ : V → M) = Subtype.val := by
    funext q
    rfl
  rw [← heq]
  exact hΦ

/-- Freeness of an action restricts to every invariant carrier. -/
private theorem restrictedIsCancelSMul_of_ambient
    {G X : Type*} [Group G] [TopologicalSpace X]
    (A : MulAction G X) (S : InvariantOpenCarrier A)
    (hfree : letI := A; IsCancelSMul G X) :
    letI := restrictedMulAction A S
    IsCancelSMul G S.carrier := by
  let _ := A
  let _ : IsCancelSMul G X := hfree
  let _ := restrictedMulAction A S
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g x hx
  apply IsCancelSMul.eq_one_of_smul (x := (x : X))
  exact congrArg Subtype.val hx

private theorem restrictedOrbitRel_eq_mulActionOrbitRel
    {G X : Type*} [Group G] [TopologicalSpace X]
    (A : MulAction G X) (S : InvariantOpenCarrier A) :
    restrictedOrbitRel A S =
      letI := restrictedMulAction A S
      MulAction.orbitRel G S.carrier := by
  rfl

/-- An equivariant diffeomorphism transports freeness from its source action to its target
action. -/
private theorem targetIsCancelSMul_of_equivariantDiffeomorph
    {G X Y : Type} [Group G] [TopologicalSpace X] [TopologicalSpace Y]
    {AX : MulAction G X} {AY : MulAction G Y}
    {S : InvariantOpenCarrier AX} {T : InvariantOpenCarrier AY}
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) S.carrier]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) T.carrier]
    (e : EquivariantOpenDiffeomorphOfActions GlobalDeckTotalModel AX AY S T)
    (hsource : letI := restrictedMulAction AX S; IsCancelSMul G S.carrier) :
    letI := restrictedMulAction AY T
    IsCancelSMul G T.carrier := by
  let _ := restrictedMulAction AY T
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g y hy
  let x := e.toDiffeomorph.symm y
  have hx : restrictedActionMap S g x = x := by
    apply e.toDiffeomorph.injective
    change e.toDiffeomorph (restrictedActionMap S g x) = e.toDiffeomorph x
    change restrictedActionMap T g y = y at hy
    calc
      e.toDiffeomorph (restrictedActionMap S g x) =
          restrictedActionMap T g (e.toDiffeomorph x) := e.equivariant g x
      _ = restrictedActionMap T g y := by rw [e.toDiffeomorph.apply_symm_apply]
      _ = y := hy
      _ = e.toDiffeomorph x := by rw [e.toDiffeomorph.apply_symm_apply]
  let _ := restrictedMulAction AX S
  let _ : IsCancelSMul G S.carrier := hsource
  exact IsCancelSMul.eq_one_of_smul (x := x) hx

/-- A local biholomorphism between covers descends to a local biholomorphism whenever both
quotient projections are locally biholomorphic. -/
public theorem quotientDescent_isLocalDiffeomorph
    {S R QS QR : Type*}
    [TopologicalSpace S] [TopologicalSpace R]
    [TopologicalSpace QS] [TopologicalSpace QR]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) S]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) R]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) QS]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) QR]
    (πS : S → QS) (πR : R → QR) (f : S → R) (fbar : QS → QR)
    (hπS : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder πS)
    (hπR : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder πR)
    (hf : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder f)
    (hcomm : fbar ∘ πS = πR ∘ f) (hπSsurj : Function.Surjective πS) :
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder fbar := by
  intro Q
  obtain ⟨x, rfl⟩ := hπSsurj Q
  let loc := (hπS x).localInverse
  have hlocx : loc (πS x) = x :=
    (hπS x).localInverse_left_inv (hπS x).localInverse_mem_target
  have hloc : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder loc (πS x) :=
    (hπS x).localInverse_isLocalDiffeomorphAt
  have hf' : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder f (loc (πS x)) := by
    rw [hlocx]
    exact hf x
  have hmiddle : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (f ∘ loc) (πS x) :=
    hloc.comp GlobalDeckTotalModel R hf'
  have hπR' : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder πR ((f ∘ loc) (πS x)) := by
    simpa [hlocx] using hπR (f x)
  have hrhs : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (πR ∘ f ∘ loc) (πS x) :=
    hmiddle.comp GlobalDeckTotalModel QR hπR'
  have hevent : fbar =ᶠ[nhds (πS x)] (πR ∘ f ∘ loc) := by
    filter_upwards [(hπS x).localInverse_eventuallyEq_right] with y hy
    calc
      fbar y = fbar (πS (loc y)) := congrArg fbar hy.symm
      _ = πR (f (loc y)) := congrFun hcomm (loc y)
  exact isLocalDiffeomorphAt_congr_of_eventuallyEq hrhs hevent.symm

/-- Inclusion of one open submanifold into a larger open submanifold is locally
biholomorphic. -/
public theorem opensInclusion_isLocalDiffeomorph
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) M]
    (V W : TopologicalSpace.Opens M) (hVW : V ≤ W) :
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (fun x : V ↦ (⟨x.1, hVW x.2⟩ : W)) := by
  intro x
  let y : W := ⟨x.1, hVW x.2⟩
  let loc := (openSubtypeVal_isLocalDiffeomorph W y).localInverse
  have hval : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (Subtype.val : V → M) x :=
    openSubtypeVal_isLocalDiffeomorph V x
  have hloc : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder loc x.1 := by
    have h := (openSubtypeVal_isLocalDiffeomorph W y).localInverse_isLocalDiffeomorphAt
    change IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder loc y.1 at h
    exact h
  have hcomp : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (loc ∘ (Subtype.val : V → M)) x :=
    hval.comp GlobalDeckTotalModel W hloc
  have hmem : (Subtype.val ⁻¹' loc.source : Set V) ∈ nhds x :=
    (loc.open_source.preimage continuous_subtype_val).mem_nhds
      (openSubtypeVal_isLocalDiffeomorph W y).localInverse_mem_source
  have hevent : (loc ∘ (Subtype.val : V → M)) =ᶠ[nhds x]
      (fun z : V ↦ (⟨z.1, hVW z.2⟩ : W)) := by
    filter_upwards [hmem] with z hz
    apply Subtype.ext
    exact (openSubtypeVal_isLocalDiffeomorph W y).localInverse_right_inv hz
  exact isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp hevent

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

/-- If the two lattice quotient projections are locally biholomorphic, the canonical map from
the regular torus family to the full torus family is complex smooth.  This is the analytic
counterpart of `regularFamilyInclusion_continuous`; it is proved on local quotient lifts. -/
public theorem regularFamilyInclusion_contMDiff_of_projection_isLocalDiffeomorph
    (hproper : SourceActionProperlyDiscontinuous (U := U)) (n : WithTop ℕ∞)
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (RegularTotalSpace F)]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hregular : letI := regularBaseChartedSpace hproper
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
        (projection (regularParameterMap F)))
    (hfull : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) :
    letI := regularBaseChartedSpace hproper
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n
      (regularFamilyInclusion F) := by
  let _ := regularBaseChartedSpace hproper
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    let πregular : RegularBase (U := U) × ComplexTwoSpace → RegularTotalSpace F :=
      projection (regularParameterMap F)
    let πfull : UpperHalfPlane × ComplexTwoSpace → TotalSpace (parameterMap F) :=
      projection (parameterMap F)
    let loc := (hregular p).localInverse
    have hlocal : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel n
        loc (πregular p) :=
      (hregular p).localInverse_contMDiffAt
    have hlocalp : loc (πregular p) = p :=
      (hregular p).localInverse_left_inv (hregular p).localInverse_mem_target
    have hmiddle : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel n
        (regularBundleInclusion ∘ loc) (πregular p) :=
      (regularBundleInclusion_contMDiff (U := U) hproper n).contMDiffAt.comp_of_eq
        hlocal hlocalp
    have hrhs : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel n
        (πfull ∘ regularBundleInclusion ∘ loc) (πregular p) :=
      (hfull (regularBundleInclusion p)).contMDiffAt.comp_of_eq hmiddle (by
        simp [hlocalp])
    have hinclusion_mk (x : RegularBase (U := U) × ComplexTwoSpace) :
        regularFamilyInclusion F (πregular x) =
          πfull (regularBundleInclusion x) := by
      dsimp only [πregular, πfull]
      rw [projection.eq_def, projection.eq_def]
      exact regularFamilyInclusion_mk F x
    have hevent : regularFamilyInclusion F =ᶠ[nhds (πregular p)]
        (πfull ∘ regularBundleInclusion ∘ loc) := by
      filter_upwards [(hregular p).localInverse_eventuallyEq_right] with y hy
      calc
        regularFamilyInclusion F y =
            regularFamilyInclusion F (πregular (loc y)) := congrArg _ hy.symm
        _ = πfull (regularBundleInclusion (loc y)) := hinclusion_mk (loc y)
    have hresult := hrhs.congr_of_eventuallyEq hevent
    have hπregularp : πregular p = Quotient.mk _ p := by
      dsimp only [πregular]
      rw [projection.eq_def]
      rfl
    rw [hπregularp] at hresult
    exact hresult

/-- If the two quotient projections are locally biholomorphic, then so is the canonical inclusion
of the regular torus family into the full family. -/
public theorem regularFamilyInclusion_isLocalDiffeomorph_of_projections
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (RegularTotalSpace F)]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hregular : letI := regularBaseChartedSpace hproper
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (projection (regularParameterMap F)))
    (hfull : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F))) :
    letI := regularBaseChartedSpace hproper
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (regularFamilyInclusion F) := by
  let _ := regularBaseChartedSpace hproper
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    let πregular : RegularBase (U := U) × ComplexTwoSpace → RegularTotalSpace F :=
      projection (regularParameterMap F)
    let πfull : UpperHalfPlane × ComplexTwoSpace → TotalSpace (parameterMap F) :=
      projection (parameterMap F)
    let loc := (hregular p).localInverse
    have hlocalp : loc (πregular p) = p :=
      (hregular p).localInverse_left_inv (hregular p).localInverse_mem_target
    have hlocal : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
        RegularSmoothnessOrder loc (πregular p) :=
      (hregular p).localInverse_isLocalDiffeomorphAt
    have hmiddle : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
        RegularSmoothnessOrder (regularBundleInclusion ∘ loc) (πregular p) :=
      hlocal.comp GlobalDeckTotalModel
        (UpperHalfPlane × ComplexTwoSpace)
        (regularBundleInclusion_isLocalDiffeomorph (U := U) hproper (loc (πregular p)))
    have hrhs : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
        RegularSmoothnessOrder (πfull ∘ regularBundleInclusion ∘ loc) (πregular p) :=
      hmiddle.comp GlobalDeckTotalModel
        (TotalSpace (parameterMap F))
        (hfull (regularBundleInclusion (loc (πregular p))))
    have hinclusion_mk (x : RegularBase (U := U) × ComplexTwoSpace) :
        regularFamilyInclusion F (πregular x) =
          πfull (regularBundleInclusion x) := by
      dsimp only [πregular, πfull]
      rw [projection.eq_def, projection.eq_def]
      exact regularFamilyInclusion_mk F x
    have hevent : regularFamilyInclusion F =ᶠ[nhds (πregular p)]
        (πfull ∘ regularBundleInclusion ∘ loc) := by
      filter_upwards [(hregular p).localInverse_eventuallyEq_right] with y hy
      calc
        regularFamilyInclusion F y =
            regularFamilyInclusion F (πregular (loc y)) := congrArg _ hy.symm
        _ = πfull (regularBundleInclusion (loc y)) := hinclusion_mk (loc y)
    have hresult := isLocalDiffeomorphAt_congr_of_eventuallyEq hrhs hevent.symm
    have hπregularp : πregular p = Quotient.mk _ p := by
      dsimp only [πregular]
      rw [projection.eq_def]
      rfl
    rw [hπregularp] at hresult
    exact hresult

/-- The canonical regular-family inclusion is unconditionally complex smooth under the source
properness already used to define the regular locus. -/
public theorem regularFamilyInclusion_contMDiff_actual
    (hproper : SourceActionProperlyDiscontinuous (U := U)) (n : WithTop ℕ∞) :
    letI := regularBaseChartedSpace hproper
    letI : LocallyCompactSpace (RegularBase (U := U)) :=
      (isOpen_isRegularBasePoint hproper).locallyCompactSpace
    letI : IsManifold GlobalDeckBaseModel n (RegularBase (U := U)) :=
      regularBase_isManifold_of_order hproper n
    letI := familyIsCancelSMul (regularParameterMap F)
    letI := familyContinuousConstSMul (regularParameterMap F)
      fun a ↦ (regularPeriodSection_contMDiff F hproper a n).continuous
    letI := familyProperlyDiscontinuousSMul (regularParameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
        (regularParameterMap_compactUniformLowerBound F))
    letI := familyIsCancelSMul (parameterMap F)
    letI := familyContinuousConstSMul (parameterMap F)
      fun a ↦ (periodSection_contMDiff F a n).continuous
    letI := familyProperlyDiscontinuousSMul (parameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap F)
        (parameterMap_compactUniformLowerBound F))
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n
      (regularFamilyInclusion F) := by
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace (RegularBase (U := U)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel n (RegularBase (U := U)) :=
    regularBase_isManifold_of_order hproper n
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    fun a ↦ (regularPeriodSection_contMDiff F hproper a n).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
      (regularParameterMap_compactUniformLowerBound F))
  let _ := familyIsCancelSMul (parameterMap F)
  let _ := familyContinuousConstSMul (parameterMap F)
    fun a ↦ (periodSection_contMDiff F a n).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap F)
      (parameterMap_compactUniformLowerBound F))
  have hregular :=
    regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph F hproper n
  have hfull := totalSpace_isManifold_and_projection_isLocalDiffeomorph F n
  exact regularFamilyInclusion_contMDiff_of_projection_isLocalDiffeomorph
    F hproper n hregular.2 hfull.2

/-- Under the established period bounds, the regular torus family is an open complex submanifold
of the full varying torus family. -/
public theorem regularFamilyInclusion_isLocalDiffeomorph_actual
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := regularBaseChartedSpace hproper
    letI : LocallyCompactSpace (RegularBase (U := U)) :=
      (isOpen_isRegularBasePoint hproper).locallyCompactSpace
    letI : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder (RegularBase (U := U)) :=
      regularBase_isManifold_of_order hproper RegularSmoothnessOrder
    letI := familyIsCancelSMul (regularParameterMap F)
    letI := familyContinuousConstSMul (regularParameterMap F)
      fun a ↦ (regularPeriodSection_contMDiff F hproper a RegularSmoothnessOrder).continuous
    letI := familyProperlyDiscontinuousSMul (regularParameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
        (regularParameterMap_compactUniformLowerBound F))
    letI := familyIsCancelSMul (parameterMap F)
    letI := familyContinuousConstSMul (parameterMap F)
      fun a ↦ (periodSection_contMDiff F a RegularSmoothnessOrder).continuous
    letI := familyProperlyDiscontinuousSMul (parameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap F)
        (parameterMap_compactUniformLowerBound F))
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (regularFamilyInclusion F) := by
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace (RegularBase (U := U)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder (RegularBase (U := U)) :=
    regularBase_isManifold_of_order hproper RegularSmoothnessOrder
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    fun a ↦ (regularPeriodSection_contMDiff F hproper a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (regularParameterMap F)
      (regularParameterMap_compactUniformLowerBound F))
  let _ := familyIsCancelSMul (parameterMap F)
  let _ := familyContinuousConstSMul (parameterMap F)
    fun a ↦ (periodSection_contMDiff F a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap F)
      (parameterMap_compactUniformLowerBound F))
  have hregular := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    F hproper RegularSmoothnessOrder
  have hfull := totalSpace_isManifold_and_projection_isLocalDiffeomorph
    F RegularSmoothnessOrder
  exact regularFamilyInclusion_isLocalDiffeomorph_of_projections
    F hproper hregular.2 hfull.2

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

@[expose] public def OrderThreeLinearCollarSourceData (r : ℝ) : Prop :=
  (∀ z : UpperHalfPlane,
      0 < ‖(orderThreeCayleyHomeomorph z : ℂ)‖ →
      ‖(orderThreeCayleyHomeomorph z : ℂ)‖ < r →
      IsRegularBasePoint (U := U) z) ∧
    ∀ z x : UpperHalfPlane,
      ‖(orderThreeCayleyHomeomorph z : ℂ)‖ < r →
      ‖(orderThreeCayleyHomeomorph x : ℂ)‖ < r →
      ∀ g : Delta, U.sourceAction g • x = z →
        ∃ a : CyclicThree, g = Monoid.Coprod.inl a

@[expose] public def OrderFourLinearCollarSourceData (r : ℝ) : Prop :=
  (∀ z : UpperHalfPlane,
      0 < ‖(orderFourCayleyHomeomorph z : ℂ)‖ →
      ‖(orderFourCayleyHomeomorph z : ℂ)‖ < r →
      IsRegularBasePoint (U := U) z) ∧
    ∀ z x : UpperHalfPlane,
      ‖(orderFourCayleyHomeomorph z : ℂ)‖ < r →
      ‖(orderFourCayleyHomeomorph x : ℂ)‖ < r →
      ∀ g : Delta, U.sourceAction g • x = z →
        ∃ a : CyclicFour, g = Monoid.Coprod.inr a

public theorem exists_orderThreeLinearCollarSourceData
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ OrderThreeLinearCollarSourceData (U := U) r := by
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianProperlyDiscontinuous_of_source hsource hproper
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g => (fuchsianSourceAction_contMDiff g 0).continuous⟩
  obtain ⟨S, hSopen, hcenterS, _hSinvariant, htranslate⟩ :=
    exists_open_stabilizer_slice (G := Delta) fuchsianOneFixedPoint
  obtain ⟨hzOne, hzTwo⟩ := ellipticFixedPoints_eq_of_fuchsian hsource
  let T := S ∩ (sourceOrbitSet (U := U) U.zTwo)ᶜ
  have hTopen : IsOpen T := hSopen.inter
    (sourceOrbitSet_isClosed hproper U.zTwo).isOpen_compl
  have hcenterNotTwo : fuchsianOneFixedPoint ∉ sourceOrbitSet (U := U) U.zTwo := by
    simp only [sourceOrbitSet.eq_def, mem_iUnion, mem_singleton_iff]
    rintro ⟨g, hg⟩
    apply fuchsianTwo_orbit_ne_one g
    simpa only [hsource, hzOne, hzTwo] using hg.symm
  have hcenterT : fuchsianOneFixedPoint ∈ T := ⟨hcenterS, hcenterNotTwo⟩
  obtain ⟨r, hr, hr1, hrT⟩ :=
    exists_cayleyRadius_subset fuchsianOneFixedPoint hTopen hcenterT
  refine ⟨r, hr, hr1, ?_⟩
  rw [OrderThreeLinearCollarSourceData.eq_def]
  constructor
  · intro z hzpos hzr
    unfold IsRegularBasePoint
    intro g
    have hzT : z ∈ T := hrT z hzr
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
      rw [hzcenter, orderThreeCayleyHomeomorph.eq_def] at hzpos
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
  obtain ⟨S, hSopen, hcenterS, _hSinvariant, htranslate⟩ :=
    exists_open_stabilizer_slice (G := Delta) fuchsianTwoFixedPoint
  obtain ⟨hzOne, hzTwo⟩ := ellipticFixedPoints_eq_of_fuchsian hsource
  let T := S ∩ (sourceOrbitSet (U := U) U.zOne)ᶜ
  have hTopen : IsOpen T := hSopen.inter
    (sourceOrbitSet_isClosed hproper U.zOne).isOpen_compl
  have hcenterNotOne : fuchsianTwoFixedPoint ∉ sourceOrbitSet (U := U) U.zOne := by
    simp only [sourceOrbitSet.eq_def, mem_iUnion, mem_singleton_iff]
    rintro ⟨g, hg⟩
    apply fuchsianOne_orbit_ne_two g
    simpa only [hsource, hzOne, hzTwo] using hg.symm
  have hcenterT : fuchsianTwoFixedPoint ∈ T := ⟨hcenterS, hcenterNotOne⟩
  obtain ⟨r, hr, hr1, hrT⟩ :=
    exists_cayleyRadius_subset fuchsianTwoFixedPoint hTopen hcenterT
  refine ⟨r, hr, hr1, ?_⟩
  rw [OrderFourLinearCollarSourceData.eq_def]
  constructor
  · intro z hzpos hzr
    unfold IsRegularBasePoint
    intro g
    have hzT : z ∈ T := hrT z hzr
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
      rw [hzcenter, orderFourCayleyHomeomorph.eq_def] at hzpos
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

/-- The order-three punctured linear collar maps locally biholomorphically to the regular torus
family. -/
public theorem orderThreeCollarToRegular_isLocalDiffeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (RegularTotalSpace F)]
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (D : OrderThreeLinearCollarSourceData (U := U) r)
    (hinclusion : letI := regularBaseChartedSpace hproper
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (regularFamilyInclusion F)) :
    letI := regularBaseChartedSpace hproper
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (orderThreeCollarToRegular F hproper D) := by
  let _ := regularBaseChartedSpace hproper
  let V : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
    ⟨orderThreePuncturedFamilyCollar F r, orderThreePuncturedFamilyCollar_isOpen F r⟩
  have hcharts : orderThreePuncturedCollarCharts F r = V.instChartedSpace := rfl
  rw [hcharts]
  intro q
  let regularPoint := orderThreeCollarToRegular F hproper D q
  let loc := (hinclusion regularPoint).localInverse
  have hqsource : (q.1 : TotalSpace (parameterMap F)) ∈ loc.source := by
    rw [← regularFamilyInclusion_orderThreeCollarToRegular F hproper D q]
    exact (hinclusion regularPoint).localInverse_mem_source
  have hloc : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder loc q.1 := by
    have h := (hinclusion regularPoint).localInverse_isLocalDiffeomorphAt
    rw [regularFamilyInclusion_orderThreeCollarToRegular F hproper D q] at h
    exact h
  have hsubtype : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (Subtype.val : V → TotalSpace (parameterMap F)) q :=
    openSubtypeVal_isLocalDiffeomorph V q
  have hcomp : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (loc ∘ (Subtype.val : V → TotalSpace (parameterMap F))) q :=
    hsubtype.comp GlobalDeckTotalModel (RegularTotalSpace F) hloc
  have hmem : (Subtype.val ⁻¹' loc.source : Set V) ∈ nhds q :=
    (loc.open_source.preimage continuous_subtype_val).mem_nhds hqsource
  have hevent : (loc ∘ (Subtype.val : V → TotalSpace (parameterMap F))) =ᶠ[nhds q]
      orderThreeCollarToRegular F hproper D := by
    filter_upwards [hmem] with y hy
    apply regularFamilyInclusion_injective F
    calc
      regularFamilyInclusion F (loc y.1) = y.1 :=
        (hinclusion regularPoint).localInverse_right_inv hy
      _ = regularFamilyInclusion F (orderThreeCollarToRegular F hproper D y) :=
        (regularFamilyInclusion_orderThreeCollarToRegular F hproper D y).symm
  exact isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp hevent

/-- The order-four punctured linear collar maps locally biholomorphically to the regular torus
family. -/
public theorem orderFourCollarToRegular_isLocalDiffeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (RegularTotalSpace F)]
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (D : OrderFourLinearCollarSourceData (U := U) r)
    (hinclusion : letI := regularBaseChartedSpace hproper
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (regularFamilyInclusion F)) :
    letI := regularBaseChartedSpace hproper
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (orderFourCollarToRegular F hproper D) := by
  let _ := regularBaseChartedSpace hproper
  let V : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
    ⟨orderFourPuncturedFamilyCollar F r, orderFourPuncturedFamilyCollar_isOpen F r⟩
  have hcharts : orderFourPuncturedCollarCharts F r = V.instChartedSpace := rfl
  rw [hcharts]
  intro q
  let regularPoint := orderFourCollarToRegular F hproper D q
  let loc := (hinclusion regularPoint).localInverse
  have hqsource : (q.1 : TotalSpace (parameterMap F)) ∈ loc.source := by
    rw [← regularFamilyInclusion_orderFourCollarToRegular F hproper D q]
    exact (hinclusion regularPoint).localInverse_mem_source
  have hloc : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder loc q.1 := by
    have h := (hinclusion regularPoint).localInverse_isLocalDiffeomorphAt
    rw [regularFamilyInclusion_orderFourCollarToRegular F hproper D q] at h
    exact h
  have hsubtype : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (Subtype.val : V → TotalSpace (parameterMap F)) q :=
    openSubtypeVal_isLocalDiffeomorph V q
  have hcomp : IsLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (loc ∘ (Subtype.val : V → TotalSpace (parameterMap F))) q :=
    hsubtype.comp GlobalDeckTotalModel (RegularTotalSpace F) hloc
  have hmem : (Subtype.val ⁻¹' loc.source : Set V) ∈ nhds q :=
    (loc.open_source.preimage continuous_subtype_val).mem_nhds hqsource
  have hevent : (loc ∘ (Subtype.val : V → TotalSpace (parameterMap F))) =ᶠ[nhds q]
      orderFourCollarToRegular F hproper D := by
    filter_upwards [hmem] with y hy
    apply regularFamilyInclusion_injective F
    calc
      regularFamilyInclusion F (loc y.1) = y.1 :=
        (hinclusion regularPoint).localInverse_right_inv hy
      _ = regularFamilyInclusion F (orderFourCollarToRegular F hproper D y) :=
        (regularFamilyInclusion_orderFourCollarToRegular F hproper D y).symm
  exact isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp hevent

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

/-- The affine order-three action remains free after restriction to its punctured collar. -/
public theorem orderThreeAffinePuncturedAction_free
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    letI := restrictedMulAction (orderThreeAffineFamilyAction F)
      (orderThreeAffinePuncturedCarrier F hsource r)
    IsCancelSMul (FiniteCyclic 3)
      (orderThreeAffinePuncturedCarrier F hsource r).carrier :=
  restrictedIsCancelSMul_of_ambient (orderThreeAffineFamilyAction F)
    (orderThreeAffinePuncturedCarrier F hsource r)
    (orderThreeAffineFamilyAction_free F hsource)

/-- The affine order-four action remains free after restriction to its punctured collar. -/
public theorem orderFourAffinePuncturedAction_free
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    letI := restrictedMulAction (orderFourAffineFamilyAction F)
      (orderFourAffinePuncturedCarrier F hsource r)
    IsCancelSMul (FiniteCyclic 4)
      (orderFourAffinePuncturedCarrier F hsource r).carrier :=
  restrictedIsCancelSMul_of_ambient (orderFourAffineFamilyAction F)
    (orderFourAffinePuncturedCarrier F hsource r)
    (orderFourAffineFamilyAction_free F hsource)

/-- The punctured linear order-three action is free: the analytic logarithmic gauge conjugates it
to the free affine action. -/
public theorem orderThreeLinearPuncturedAction_free
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel (⊤ : WithTop ℕ∞)
      (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      (⊤ : WithTop ℕ∞) (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    letI := restrictedMulAction (orderThreeLinearFamilyAction F)
      (orderThreeLinearPuncturedCarrier F hsource r)
    IsCancelSMul (FiniteCyclic 3)
      (orderThreeLinearPuncturedCarrier F hsource r).carrier := by
  apply targetIsCancelSMul_of_equivariantDiffeomorph
    (orderThreePuncturedGaugeEquivariantDiffeomorph F hprojection hsource r)
  exact orderThreeAffinePuncturedAction_free F hsource r

/-- The punctured linear order-four action is free by the same analytic gauge conjugacy. -/
public theorem orderFourLinearPuncturedAction_free
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel (⊤ : WithTop ℕ∞)
      (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      (⊤ : WithTop ℕ∞) (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    letI := restrictedMulAction (orderFourLinearFamilyAction F)
      (orderFourLinearPuncturedCarrier F hsource r)
    IsCancelSMul (FiniteCyclic 4)
      (orderFourLinearPuncturedCarrier F hsource r).carrier := by
  apply targetIsCancelSMul_of_equivariantDiffeomorph
    (orderFourPuncturedGaugeEquivariantDiffeomorph F hprojection hsource r)
  exact orderFourAffinePuncturedAction_free F hsource r

/-- Each restricted affine order-three deck map is complex smooth. -/
public theorem orderThreeAffinePuncturedAction_contMDiff
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ)
    (g : FiniteCyclic 3) :
    letI := restrictedMulAction (orderThreeAffineFamilyAction F)
      (orderThreeAffinePuncturedCarrier F hsource r)
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (fun q : (orderThreeAffinePuncturedCarrier F hsource r).carrier ↦ g • q) := by
  let _ := restrictedMulAction (orderThreeAffineFamilyAction F)
    (orderThreeAffinePuncturedCarrier F hsource r)
  let V : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
    ⟨(orderThreeAffinePuncturedCarrier F hsource r).carrier,
      (orderThreeAffinePuncturedCarrier F hsource r).isOpen_carrier⟩
  have hcharts : orderThreeAffinePuncturedCarrierCharts F hsource r =
      V.instChartedSpace := rfl
  rw [hcharts]
  intro q
  apply (ContMDiffAt.subtypeVal_comp_iff V _ q).mp
  exact (orderThreeAffineFamilyRepresentation_contMDiff F hprojection g).contMDiffAt.comp
    q (contMDiff_subtype_val (I := GlobalDeckTotalModel) (U := V)).contMDiffAt

/-- Each restricted affine order-four deck map is complex smooth. -/
public theorem orderFourAffinePuncturedAction_contMDiff
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ)
    (g : FiniteCyclic 4) :
    letI := restrictedMulAction (orderFourAffineFamilyAction F)
      (orderFourAffinePuncturedCarrier F hsource r)
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (fun q : (orderFourAffinePuncturedCarrier F hsource r).carrier ↦ g • q) := by
  let _ := restrictedMulAction (orderFourAffineFamilyAction F)
    (orderFourAffinePuncturedCarrier F hsource r)
  let V : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
    ⟨(orderFourAffinePuncturedCarrier F hsource r).carrier,
      (orderFourAffinePuncturedCarrier F hsource r).isOpen_carrier⟩
  have hcharts : orderFourAffinePuncturedCarrierCharts F hsource r =
      V.instChartedSpace := rfl
  rw [hcharts]
  intro q
  apply (ContMDiffAt.subtypeVal_comp_iff V _ q).mp
  exact (orderFourAffineFamilyRepresentation_contMDiff F hprojection g).contMDiffAt.comp
    q (contMDiff_subtype_val (I := GlobalDeckTotalModel) (U := V)).contMDiffAt

/-- Each restricted linear order-three deck map is complex smooth. -/
public theorem orderThreeLinearPuncturedAction_contMDiff
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ)
    (g : FiniteCyclic 3) :
    letI := restrictedMulAction (orderThreeLinearFamilyAction F)
      (orderThreeLinearPuncturedCarrier F hsource r)
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (fun q : (orderThreeLinearPuncturedCarrier F hsource r).carrier ↦ g • q) := by
  let _ := restrictedMulAction (orderThreeLinearFamilyAction F)
    (orderThreeLinearPuncturedCarrier F hsource r)
  let V : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
    ⟨(orderThreeLinearPuncturedCarrier F hsource r).carrier,
      (orderThreeLinearPuncturedCarrier F hsource r).isOpen_carrier⟩
  have hcharts : orderThreeLinearPuncturedCarrierCharts F hsource r =
      V.instChartedSpace := rfl
  rw [hcharts]
  intro q
  apply (ContMDiffAt.subtypeVal_comp_iff V _ q).mp
  exact (familyDeckMap_contMDiff_of_projection_isLocalDiffeomorph F
    RegularSmoothnessOrder hprojection (Monoid.Coprod.inl g)).contMDiffAt.comp
      q (contMDiff_subtype_val (I := GlobalDeckTotalModel) (U := V)).contMDiffAt

/-- Each restricted linear order-four deck map is complex smooth. -/
public theorem orderFourLinearPuncturedAction_contMDiff
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ)
    (g : FiniteCyclic 4) :
    letI := restrictedMulAction (orderFourLinearFamilyAction F)
      (orderFourLinearPuncturedCarrier F hsource r)
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (fun q : (orderFourLinearPuncturedCarrier F hsource r).carrier ↦ g • q) := by
  let _ := restrictedMulAction (orderFourLinearFamilyAction F)
    (orderFourLinearPuncturedCarrier F hsource r)
  let V : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
    ⟨(orderFourLinearPuncturedCarrier F hsource r).carrier,
      (orderFourLinearPuncturedCarrier F hsource r).isOpen_carrier⟩
  have hcharts : orderFourLinearPuncturedCarrierCharts F hsource r =
      V.instChartedSpace := rfl
  rw [hcharts]
  intro q
  apply (ContMDiffAt.subtypeVal_comp_iff V _ q).mp
  exact (familyDeckMap_contMDiff_of_projection_isLocalDiffeomorph F
    RegularSmoothnessOrder hprojection (Monoid.Coprod.inr g)).contMDiffAt.comp
      q (contMDiff_subtype_val (I := GlobalDeckTotalModel) (U := V)).contMDiffAt

@[instance_reducible]
public noncomputable def orderThreeAffinePuncturedQuotientCharts
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    [T2Space (TotalSpace (parameterMap F))]
    [LocallyCompactSpace (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction F)
        (orderThreeAffinePuncturedCarrier F hsource r))) := by
  let _ := restrictedMulAction (orderThreeAffineFamilyAction F)
    (orderThreeAffinePuncturedCarrier F hsource r)
  let _ : IsCancelSMul (FiniteCyclic 3)
      (orderThreeAffinePuncturedCarrier F hsource r).carrier :=
    orderThreeAffinePuncturedAction_free F hsource r
  let _ : ContinuousConstSMul (FiniteCyclic 3)
      (orderThreeAffinePuncturedCarrier F hsource r).carrier :=
    ⟨fun g ↦ (orderThreeAffinePuncturedAction_contMDiff
      F hprojection hsource r g).continuous⟩
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic 3)
      (orderThreeAffinePuncturedCarrier F hsource r).carrier := by infer_instance
  let _ : LocallyCompactSpace
      (orderThreeAffinePuncturedCarrier F hsource r).carrier :=
    (orderThreeAffinePuncturedCarrier F hsource r).isOpen_carrier.locallyCompactSpace
  let _ : T2Space (orderThreeAffinePuncturedCarrier F hsource r).carrier := by
    infer_instance
  rw [restrictedOrbitRel_eq_mulActionOrbitRel]
  infer_instance

@[instance_reducible]
public noncomputable def orderFourAffinePuncturedQuotientCharts
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    [T2Space (TotalSpace (parameterMap F))]
    [LocallyCompactSpace (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (Quotient (restrictedOrbitRel (orderFourAffineFamilyAction F)
        (orderFourAffinePuncturedCarrier F hsource r))) := by
  let _ := restrictedMulAction (orderFourAffineFamilyAction F)
    (orderFourAffinePuncturedCarrier F hsource r)
  let _ : IsCancelSMul (FiniteCyclic 4)
      (orderFourAffinePuncturedCarrier F hsource r).carrier :=
    orderFourAffinePuncturedAction_free F hsource r
  let _ : ContinuousConstSMul (FiniteCyclic 4)
      (orderFourAffinePuncturedCarrier F hsource r).carrier :=
    ⟨fun g ↦ (orderFourAffinePuncturedAction_contMDiff
      F hprojection hsource r g).continuous⟩
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic 4)
      (orderFourAffinePuncturedCarrier F hsource r).carrier := by infer_instance
  let _ : LocallyCompactSpace
      (orderFourAffinePuncturedCarrier F hsource r).carrier :=
    (orderFourAffinePuncturedCarrier F hsource r).isOpen_carrier.locallyCompactSpace
  let _ : T2Space (orderFourAffinePuncturedCarrier F hsource r).carrier := by
    infer_instance
  rw [restrictedOrbitRel_eq_mulActionOrbitRel]
  infer_instance

@[instance_reducible]
public noncomputable def orderThreeLinearPuncturedQuotientCharts
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    [T2Space (TotalSpace (parameterMap F))]
    [LocallyCompactSpace (TotalSpace (parameterMap F))]
    (hprojectionAnalytic : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F)))
    (hprojectionSmooth : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (Quotient (restrictedOrbitRel (orderThreeLinearFamilyAction F)
        (orderThreeLinearPuncturedCarrier F hsource r))) := by
  let _ := restrictedMulAction (orderThreeLinearFamilyAction F)
    (orderThreeLinearPuncturedCarrier F hsource r)
  let _ : IsCancelSMul (FiniteCyclic 3)
      (orderThreeLinearPuncturedCarrier F hsource r).carrier :=
    orderThreeLinearPuncturedAction_free F hprojectionAnalytic hsource r
  let _ : ContinuousConstSMul (FiniteCyclic 3)
      (orderThreeLinearPuncturedCarrier F hsource r).carrier :=
    ⟨fun g ↦ (orderThreeLinearPuncturedAction_contMDiff
      F hprojectionSmooth hsource r g).continuous⟩
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic 3)
      (orderThreeLinearPuncturedCarrier F hsource r).carrier := by infer_instance
  let _ : LocallyCompactSpace
      (orderThreeLinearPuncturedCarrier F hsource r).carrier :=
    (orderThreeLinearPuncturedCarrier F hsource r).isOpen_carrier.locallyCompactSpace
  let _ : T2Space (orderThreeLinearPuncturedCarrier F hsource r).carrier := by
    infer_instance
  rw [restrictedOrbitRel_eq_mulActionOrbitRel]
  infer_instance

@[instance_reducible]
public noncomputable def orderFourLinearPuncturedQuotientCharts
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    [T2Space (TotalSpace (parameterMap F))]
    [LocallyCompactSpace (TotalSpace (parameterMap F))]
    (hprojectionAnalytic : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F)))
    (hprojectionSmooth : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (Quotient (restrictedOrbitRel (orderFourLinearFamilyAction F)
        (orderFourLinearPuncturedCarrier F hsource r))) := by
  let _ := restrictedMulAction (orderFourLinearFamilyAction F)
    (orderFourLinearPuncturedCarrier F hsource r)
  let _ : IsCancelSMul (FiniteCyclic 4)
      (orderFourLinearPuncturedCarrier F hsource r).carrier :=
    orderFourLinearPuncturedAction_free F hprojectionAnalytic hsource r
  let _ : ContinuousConstSMul (FiniteCyclic 4)
      (orderFourLinearPuncturedCarrier F hsource r).carrier :=
    ⟨fun g ↦ (orderFourLinearPuncturedAction_contMDiff
      F hprojectionSmooth hsource r g).continuous⟩
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic 4)
      (orderFourLinearPuncturedCarrier F hsource r).carrier := by infer_instance
  let _ : LocallyCompactSpace
      (orderFourLinearPuncturedCarrier F hsource r).carrier :=
    (orderFourLinearPuncturedCarrier F hsource r).isOpen_carrier.locallyCompactSpace
  let _ : T2Space (orderFourLinearPuncturedCarrier F hsource r).carrier := by
    infer_instance
  rw [restrictedOrbitRel_eq_mulActionOrbitRel]
  infer_instance

/-- The punctured affine order-three quotient is a complex manifold and its projection is
locally biholomorphic. -/
public theorem orderThreeAffinePuncturedQuotient_isManifold_and_projection_isLocalDiffeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    [T2Space (TotalSpace (parameterMap F))]
    [LocallyCompactSpace (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    letI := restrictedMulAction (orderThreeAffineFamilyAction F)
      (orderThreeAffinePuncturedCarrier F hsource r)
    letI := orderThreeAffinePuncturedAction_free F hsource r
    letI : ContinuousConstSMul (FiniteCyclic 3)
        (orderThreeAffinePuncturedCarrier F hsource r).carrier :=
      ⟨fun g ↦ (orderThreeAffinePuncturedAction_contMDiff
        F hprojection hsource r g).continuous⟩
    letI := orderThreeAffinePuncturedQuotientCharts F hprojection hsource r
    IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
        (Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction F)
          (orderThreeAffinePuncturedCarrier F hsource r))) ∧
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
        RegularSmoothnessOrder
        (Quotient.mk (restrictedOrbitRel (orderThreeAffineFamilyAction F)
          (orderThreeAffinePuncturedCarrier F hsource r))) := by
  let _ := restrictedMulAction (orderThreeAffineFamilyAction F)
    (orderThreeAffinePuncturedCarrier F hsource r)
  let _ : IsCancelSMul (FiniteCyclic 3)
      (orderThreeAffinePuncturedCarrier F hsource r).carrier :=
    orderThreeAffinePuncturedAction_free F hsource r
  let _ : ContinuousConstSMul (FiniteCyclic 3)
      (orderThreeAffinePuncturedCarrier F hsource r).carrier :=
    ⟨fun g ↦ (orderThreeAffinePuncturedAction_contMDiff
      F hprojection hsource r g).continuous⟩
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic 3)
      (orderThreeAffinePuncturedCarrier F hsource r).carrier := by infer_instance
  let _ := orderThreeAffinePuncturedQuotientCharts F hprojection hsource r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (orderThreeAffinePuncturedCarrier F hsource r).carrier := by
    let V : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
      ⟨(orderThreeAffinePuncturedCarrier F hsource r).carrier,
        (orderThreeAffinePuncturedCarrier F hsource r).isOpen_carrier⟩
    have hcharts : orderThreeAffinePuncturedCarrierCharts F hsource r =
        V.instChartedSpace := rfl
    rw [hcharts]
    change IsManifold GlobalDeckTotalModel RegularSmoothnessOrder V
    infer_instance
  let _ : LocallyCompactSpace
      (orderThreeAffinePuncturedCarrier F hsource r).carrier :=
    (orderThreeAffinePuncturedCarrier F hsource r).isOpen_carrier.locallyCompactSpace
  let _ : T2Space (orderThreeAffinePuncturedCarrier F hsource r).carrier := by
    infer_instance
  exact orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    GlobalDeckTotalModel RegularSmoothnessOrder
      (orderThreeAffinePuncturedAction_contMDiff F hprojection hsource r)

/-- The punctured affine order-four quotient has the analogous locally biholomorphic quotient
projection. -/
public theorem orderFourAffinePuncturedQuotient_isManifold_and_projection_isLocalDiffeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    [T2Space (TotalSpace (parameterMap F))]
    [LocallyCompactSpace (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    letI := restrictedMulAction (orderFourAffineFamilyAction F)
      (orderFourAffinePuncturedCarrier F hsource r)
    letI := orderFourAffinePuncturedAction_free F hsource r
    letI : ContinuousConstSMul (FiniteCyclic 4)
        (orderFourAffinePuncturedCarrier F hsource r).carrier :=
      ⟨fun g ↦ (orderFourAffinePuncturedAction_contMDiff
        F hprojection hsource r g).continuous⟩
    letI := orderFourAffinePuncturedQuotientCharts F hprojection hsource r
    IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
        (Quotient (restrictedOrbitRel (orderFourAffineFamilyAction F)
          (orderFourAffinePuncturedCarrier F hsource r))) ∧
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
        RegularSmoothnessOrder
        (Quotient.mk (restrictedOrbitRel (orderFourAffineFamilyAction F)
          (orderFourAffinePuncturedCarrier F hsource r))) := by
  let _ := restrictedMulAction (orderFourAffineFamilyAction F)
    (orderFourAffinePuncturedCarrier F hsource r)
  let _ : IsCancelSMul (FiniteCyclic 4)
      (orderFourAffinePuncturedCarrier F hsource r).carrier :=
    orderFourAffinePuncturedAction_free F hsource r
  let _ : ContinuousConstSMul (FiniteCyclic 4)
      (orderFourAffinePuncturedCarrier F hsource r).carrier :=
    ⟨fun g ↦ (orderFourAffinePuncturedAction_contMDiff
      F hprojection hsource r g).continuous⟩
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic 4)
      (orderFourAffinePuncturedCarrier F hsource r).carrier := by infer_instance
  let _ := orderFourAffinePuncturedQuotientCharts F hprojection hsource r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (orderFourAffinePuncturedCarrier F hsource r).carrier := by
    let V : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
      ⟨(orderFourAffinePuncturedCarrier F hsource r).carrier,
        (orderFourAffinePuncturedCarrier F hsource r).isOpen_carrier⟩
    have hcharts : orderFourAffinePuncturedCarrierCharts F hsource r =
        V.instChartedSpace := rfl
    rw [hcharts]
    change IsManifold GlobalDeckTotalModel RegularSmoothnessOrder V
    infer_instance
  let _ : LocallyCompactSpace
      (orderFourAffinePuncturedCarrier F hsource r).carrier :=
    (orderFourAffinePuncturedCarrier F hsource r).isOpen_carrier.locallyCompactSpace
  let _ : T2Space (orderFourAffinePuncturedCarrier F hsource r).carrier := by
    infer_instance
  exact orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    GlobalDeckTotalModel RegularSmoothnessOrder
      (orderFourAffinePuncturedAction_contMDiff F hprojection hsource r)

/-- The punctured linear order-three quotient is a complex manifold and its projection is
locally biholomorphic.  Analyticity of the total-family projection supplies the gauge used to
prove freeness, while smoothness supplies the quotient atlas. -/
public theorem orderThreeLinearPuncturedQuotient_isManifold_and_projection_isLocalDiffeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    [T2Space (TotalSpace (parameterMap F))]
    [LocallyCompactSpace (TotalSpace (parameterMap F))]
    (hprojectionAnalytic : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F)))
    (hprojectionSmooth : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    letI := restrictedMulAction (orderThreeLinearFamilyAction F)
      (orderThreeLinearPuncturedCarrier F hsource r)
    letI := orderThreeLinearPuncturedAction_free F hprojectionAnalytic hsource r
    letI : ContinuousConstSMul (FiniteCyclic 3)
        (orderThreeLinearPuncturedCarrier F hsource r).carrier :=
      ⟨fun g ↦ (orderThreeLinearPuncturedAction_contMDiff
        F hprojectionSmooth hsource r g).continuous⟩
    letI := orderThreeLinearPuncturedQuotientCharts F hprojectionAnalytic
      hprojectionSmooth hsource r
    IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
        (Quotient (restrictedOrbitRel (orderThreeLinearFamilyAction F)
          (orderThreeLinearPuncturedCarrier F hsource r))) ∧
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
        RegularSmoothnessOrder
        (Quotient.mk (restrictedOrbitRel (orderThreeLinearFamilyAction F)
          (orderThreeLinearPuncturedCarrier F hsource r))) := by
  let _ := restrictedMulAction (orderThreeLinearFamilyAction F)
    (orderThreeLinearPuncturedCarrier F hsource r)
  let _ : IsCancelSMul (FiniteCyclic 3)
      (orderThreeLinearPuncturedCarrier F hsource r).carrier :=
    orderThreeLinearPuncturedAction_free F hprojectionAnalytic hsource r
  let _ : ContinuousConstSMul (FiniteCyclic 3)
      (orderThreeLinearPuncturedCarrier F hsource r).carrier :=
    ⟨fun g ↦ (orderThreeLinearPuncturedAction_contMDiff
      F hprojectionSmooth hsource r g).continuous⟩
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic 3)
      (orderThreeLinearPuncturedCarrier F hsource r).carrier := by infer_instance
  let _ := orderThreeLinearPuncturedQuotientCharts F hprojectionAnalytic
    hprojectionSmooth hsource r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (orderThreeLinearPuncturedCarrier F hsource r).carrier := by
    let V : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
      ⟨(orderThreeLinearPuncturedCarrier F hsource r).carrier,
        (orderThreeLinearPuncturedCarrier F hsource r).isOpen_carrier⟩
    have hcharts : orderThreeLinearPuncturedCarrierCharts F hsource r =
        V.instChartedSpace := rfl
    rw [hcharts]
    change IsManifold GlobalDeckTotalModel RegularSmoothnessOrder V
    infer_instance
  let _ : LocallyCompactSpace
      (orderThreeLinearPuncturedCarrier F hsource r).carrier :=
    (orderThreeLinearPuncturedCarrier F hsource r).isOpen_carrier.locallyCompactSpace
  let _ : T2Space (orderThreeLinearPuncturedCarrier F hsource r).carrier := by
    infer_instance
  exact orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    GlobalDeckTotalModel RegularSmoothnessOrder
      (orderThreeLinearPuncturedAction_contMDiff F hprojectionSmooth hsource r)

/-- The punctured linear order-four quotient has the analogous analytic quotient projection. -/
public theorem orderFourLinearPuncturedQuotient_isManifold_and_projection_isLocalDiffeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    [T2Space (TotalSpace (parameterMap F))]
    [LocallyCompactSpace (TotalSpace (parameterMap F))]
    (hprojectionAnalytic : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F)))
    (hprojectionSmooth : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    letI := restrictedMulAction (orderFourLinearFamilyAction F)
      (orderFourLinearPuncturedCarrier F hsource r)
    letI := orderFourLinearPuncturedAction_free F hprojectionAnalytic hsource r
    letI : ContinuousConstSMul (FiniteCyclic 4)
        (orderFourLinearPuncturedCarrier F hsource r).carrier :=
      ⟨fun g ↦ (orderFourLinearPuncturedAction_contMDiff
        F hprojectionSmooth hsource r g).continuous⟩
    letI := orderFourLinearPuncturedQuotientCharts F hprojectionAnalytic
      hprojectionSmooth hsource r
    IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
        (Quotient (restrictedOrbitRel (orderFourLinearFamilyAction F)
          (orderFourLinearPuncturedCarrier F hsource r))) ∧
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
        RegularSmoothnessOrder
        (Quotient.mk (restrictedOrbitRel (orderFourLinearFamilyAction F)
          (orderFourLinearPuncturedCarrier F hsource r))) := by
  let _ := restrictedMulAction (orderFourLinearFamilyAction F)
    (orderFourLinearPuncturedCarrier F hsource r)
  let _ : IsCancelSMul (FiniteCyclic 4)
      (orderFourLinearPuncturedCarrier F hsource r).carrier :=
    orderFourLinearPuncturedAction_free F hprojectionAnalytic hsource r
  let _ : ContinuousConstSMul (FiniteCyclic 4)
      (orderFourLinearPuncturedCarrier F hsource r).carrier :=
    ⟨fun g ↦ (orderFourLinearPuncturedAction_contMDiff
      F hprojectionSmooth hsource r g).continuous⟩
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic 4)
      (orderFourLinearPuncturedCarrier F hsource r).carrier := by infer_instance
  let _ := orderFourLinearPuncturedQuotientCharts F hprojectionAnalytic
    hprojectionSmooth hsource r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (orderFourLinearPuncturedCarrier F hsource r).carrier := by
    let V : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
      ⟨(orderFourLinearPuncturedCarrier F hsource r).carrier,
        (orderFourLinearPuncturedCarrier F hsource r).isOpen_carrier⟩
    have hcharts : orderFourLinearPuncturedCarrierCharts F hsource r =
        V.instChartedSpace := rfl
    rw [hcharts]
    change IsManifold GlobalDeckTotalModel RegularSmoothnessOrder V
    infer_instance
  let _ : LocallyCompactSpace
      (orderFourLinearPuncturedCarrier F hsource r).carrier :=
    (orderFourLinearPuncturedCarrier F hsource r).isOpen_carrier.locallyCompactSpace
  let _ : T2Space (orderFourLinearPuncturedCarrier F hsource r).carrier := by
    infer_instance
  exact orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    GlobalDeckTotalModel RegularSmoothnessOrder
      (orderFourLinearPuncturedAction_contMDiff F hprojectionSmooth hsource r)

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

/-- After applying the logarithmic gauge, the affine order-three collar action becomes the
literal `Delta` deck action on the regular family. -/
public theorem orderThreeAffineCollarLift_action
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderThreeLinearCollarSourceData (U := U) r)
    (a : FiniteCyclic 3)
    (q : (orderThreeAffinePuncturedCarrier F hsource r).carrier) :
    orderThreeCollarToRegular F hproper D
        (orderThreePuncturedCollarGaugeDiffeomorph F hprojection r
          (restrictedActionMap (orderThreeAffinePuncturedCarrier F hsource r) a q)) =
      regularFamilyDeckMap F (Monoid.Coprod.inl a)
        (orderThreeCollarToRegular F hproper D
          (orderThreePuncturedCollarGaugeDiffeomorph F hprojection r q)) := by
  have hgauge :
      orderThreePuncturedCollarGaugeDiffeomorph F hprojection r
          (restrictedActionMap (orderThreeAffinePuncturedCarrier F hsource r) a q) =
        restrictedActionMap (orderThreeLinearPuncturedCarrier F hsource r) a
          (orderThreePuncturedCollarGaugeDiffeomorph F hprojection r q) :=
    (orderThreePuncturedGaugeEquivariantDiffeomorph F hprojection hsource r).equivariant a q
  rw [hgauge]
  exact orderThreeCollarToRegular_action F hproper hsource D a
    (orderThreePuncturedCollarGaugeDiffeomorph F hprojection r q)

/-- The corresponding affine-to-regular equivariance for the order-four collar. -/
public theorem orderFourAffineCollarLift_action
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderFourLinearCollarSourceData (U := U) r)
    (a : FiniteCyclic 4)
    (q : (orderFourAffinePuncturedCarrier F hsource r).carrier) :
    orderFourCollarToRegular F hproper D
        (orderFourPuncturedCollarGaugeDiffeomorph F hprojection r
          (restrictedActionMap (orderFourAffinePuncturedCarrier F hsource r) a q)) =
      regularFamilyDeckMap F (Monoid.Coprod.inr a)
        (orderFourCollarToRegular F hproper D
          (orderFourPuncturedCollarGaugeDiffeomorph F hprojection r q)) := by
  have hgauge :
      orderFourPuncturedCollarGaugeDiffeomorph F hprojection r
          (restrictedActionMap (orderFourAffinePuncturedCarrier F hsource r) a q) =
        restrictedActionMap (orderFourLinearPuncturedCarrier F hsource r) a
          (orderFourPuncturedCollarGaugeDiffeomorph F hprojection r q) :=
    (orderFourPuncturedGaugeEquivariantDiffeomorph F hprojection hsource r).equivariant a q
  rw [hgauge]
  exact orderFourCollarToRegular_action F hproper hsource D a
    (orderFourPuncturedCollarGaugeDiffeomorph F hprojection r q)

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

/-- Descent through the two quotient projections upgrades the order-three linear collar map to a
local biholomorphism. -/
public theorem orderThreeLinearCollarToPuncturedGlobalFamily_isLocalDiffeomorph_of_projections
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    [T2Space (TotalSpace (parameterMap F))]
    [LocallyCompactSpace (TotalSpace (parameterMap F))]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (RegularTotalSpace F)]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (PuncturedGlobalFamily F)]
    (hprojectionAnalytic : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F)))
    (hprojectionSmooth : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderThreeLinearCollarSourceData (U := U) r)
    (hcollar : letI := regularBaseChartedSpace hproper
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (orderThreeCollarToRegular F hproper D))
    (htarget : letI := regularFamilyDeckAction F
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (Quotient.mk (MulAction.orbitRel Delta (RegularTotalSpace F)))) :
    letI := orderThreeLinearPuncturedQuotientCharts F hprojectionAnalytic
      hprojectionSmooth hsource r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (orderThreeLinearCollarToPuncturedGlobalFamily F hproper hsource D) := by
  let _ := regularBaseChartedSpace hproper
  let _ := restrictedMulAction (orderThreeLinearFamilyAction F)
    (orderThreeLinearPuncturedCarrier F hsource r)
  let _ : IsCancelSMul (FiniteCyclic 3)
      (orderThreeLinearPuncturedCarrier F hsource r).carrier :=
    orderThreeLinearPuncturedAction_free F hprojectionAnalytic hsource r
  let _ : ContinuousConstSMul (FiniteCyclic 3)
      (orderThreeLinearPuncturedCarrier F hsource r).carrier :=
    ⟨fun g ↦ (orderThreeLinearPuncturedAction_contMDiff
      F hprojectionSmooth hsource r g).continuous⟩
  let _ := orderThreeLinearPuncturedQuotientCharts F hprojectionAnalytic
    hprojectionSmooth hsource r
  let _ := regularFamilyDeckAction F
  have hsourceProjection :=
    (orderThreeLinearPuncturedQuotient_isManifold_and_projection_isLocalDiffeomorph
      F hprojectionAnalytic hprojectionSmooth hsource r).2
  apply quotientDescent_isLocalDiffeomorph
    (Quotient.mk (restrictedOrbitRel (orderThreeLinearFamilyAction F)
      (orderThreeLinearPuncturedCarrier F hsource r)))
    (Quotient.mk (MulAction.orbitRel Delta (RegularTotalSpace F)))
    (orderThreeCollarToRegular F hproper D)
    (orderThreeLinearCollarToPuncturedGlobalFamily F hproper hsource D)
    hsourceProjection htarget hcollar
  · funext q
    exact orderThreeLinearCollarToPuncturedGlobalFamily_mk F hproper hsource D q
  · exact Quotient.mk_surjective

/-- Descent through the two quotient projections gives the analogous order-four local
biholomorphism. -/
public theorem orderFourLinearCollarToPuncturedGlobalFamily_isLocalDiffeomorph_of_projections
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    [T2Space (TotalSpace (parameterMap F))]
    [LocallyCompactSpace (TotalSpace (parameterMap F))]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (RegularTotalSpace F)]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (PuncturedGlobalFamily F)]
    (hprojectionAnalytic : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F)))
    (hprojectionSmooth : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderFourLinearCollarSourceData (U := U) r)
    (hcollar : letI := regularBaseChartedSpace hproper
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (orderFourCollarToRegular F hproper D))
    (htarget : letI := regularFamilyDeckAction F
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (Quotient.mk (MulAction.orbitRel Delta (RegularTotalSpace F)))) :
    letI := orderFourLinearPuncturedQuotientCharts F hprojectionAnalytic
      hprojectionSmooth hsource r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (orderFourLinearCollarToPuncturedGlobalFamily F hproper hsource D) := by
  let _ := regularBaseChartedSpace hproper
  let _ := restrictedMulAction (orderFourLinearFamilyAction F)
    (orderFourLinearPuncturedCarrier F hsource r)
  let _ : IsCancelSMul (FiniteCyclic 4)
      (orderFourLinearPuncturedCarrier F hsource r).carrier :=
    orderFourLinearPuncturedAction_free F hprojectionAnalytic hsource r
  let _ : ContinuousConstSMul (FiniteCyclic 4)
      (orderFourLinearPuncturedCarrier F hsource r).carrier :=
    ⟨fun g ↦ (orderFourLinearPuncturedAction_contMDiff
      F hprojectionSmooth hsource r g).continuous⟩
  let _ := orderFourLinearPuncturedQuotientCharts F hprojectionAnalytic
    hprojectionSmooth hsource r
  let _ := regularFamilyDeckAction F
  have hsourceProjection :=
    (orderFourLinearPuncturedQuotient_isManifold_and_projection_isLocalDiffeomorph
      F hprojectionAnalytic hprojectionSmooth hsource r).2
  apply quotientDescent_isLocalDiffeomorph
    (Quotient.mk (restrictedOrbitRel (orderFourLinearFamilyAction F)
      (orderFourLinearPuncturedCarrier F hsource r)))
    (Quotient.mk (MulAction.orbitRel Delta (RegularTotalSpace F)))
    (orderFourCollarToRegular F hproper D)
    (orderFourLinearCollarToPuncturedGlobalFamily F hproper hsource D)
    hsourceProjection htarget hcollar
  · funext q
    exact orderFourLinearCollarToPuncturedGlobalFamily_mk F hproper hsource D q
  · exact Quotient.mk_surjective

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
        (by simpa only [orderThreePuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
          orderThreeFamilyRadius.eq_def] using q.property.2)
        (by simpa only [orderThreePuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
          orderThreeFamilyRadius.eq_def] using x.property.2) g hbase
      apply Quotient.sound
      let _ := restrictedMulAction (orderThreeLinearFamilyAction F)
        (orderThreeLinearPuncturedCarrier F hsource r)
      change MulAction.orbitRel (FiniteCyclic 3) _ q x
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change actionMap (orderThreeLinearFamilyAction F) a x = q
      rw [orderThreeLinear_actionMap, ← ha]
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
        (by simpa only [orderFourPuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
          orderFourFamilyRadius.eq_def] using q.property.2)
        (by simpa only [orderFourPuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
          orderFourFamilyRadius.eq_def] using x.property.2) g hbase
      apply Quotient.sound
      let _ := restrictedMulAction (orderFourLinearFamilyAction F)
        (orderFourLinearPuncturedCarrier F hsource r)
      change MulAction.orbitRel (FiniteCyclic 4) _ q x
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨a, ?_⟩
      apply Subtype.ext
      change actionMap (orderFourLinearFamilyAction F) a x = q
      rw [orderFourLinear_actionMap, ← ha]
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

@[simp]
public theorem orderThreeAffineCollarToPuncturedGlobalFamily_mk
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderThreeLinearCollarSourceData (U := U) r)
    (q : (orderThreeAffinePuncturedCarrier F hsource r).carrier) :
    orderThreeAffineCollarToPuncturedGlobalFamily F hprojection hproper hsource D
        (Quotient.mk _ q) =
      Quotient.mk _ (orderThreeCollarToRegular F hproper D
        (orderThreePuncturedCollarGaugeDiffeomorph F hprojection r q)) :=
  rfl

@[simp]
public theorem orderFourAffineCollarToPuncturedGlobalFamily_mk
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderFourLinearCollarSourceData (U := U) r)
    (q : (orderFourAffinePuncturedCarrier F hsource r).carrier) :
    orderFourAffineCollarToPuncturedGlobalFamily F hprojection hproper hsource D
        (Quotient.mk _ q) =
      Quotient.mk _ (orderFourCollarToRegular F hproper D
        (orderFourPuncturedCollarGaugeDiffeomorph F hprojection r q)) :=
  rfl

/-- With the canonical quotient atlases, the logarithmically gauged order-three affine collar
map is locally biholomorphic. -/
public theorem orderThreeAffineCollarToPuncturedGlobalFamily_isLocalDiffeomorph_of_projections
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    [T2Space (TotalSpace (parameterMap F))]
    [LocallyCompactSpace (TotalSpace (parameterMap F))]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (RegularTotalSpace F)]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (PuncturedGlobalFamily F)]
    (hprojectionAnalytic : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F)))
    (hprojectionSmooth : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderThreeLinearCollarSourceData (U := U) r)
    (hcollar : letI := regularBaseChartedSpace hproper
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (orderThreeCollarToRegular F hproper D))
    (htarget : letI := regularFamilyDeckAction F
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (Quotient.mk (MulAction.orbitRel Delta (RegularTotalSpace F)))) :
    letI := orderThreeAffinePuncturedQuotientCharts F hprojectionSmooth hsource r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (orderThreeAffineCollarToPuncturedGlobalFamily
        F hprojectionAnalytic hproper hsource D) := by
  let _ := regularBaseChartedSpace hproper
  let _ := restrictedMulAction (orderThreeAffineFamilyAction F)
    (orderThreeAffinePuncturedCarrier F hsource r)
  let _ : IsCancelSMul (FiniteCyclic 3)
      (orderThreeAffinePuncturedCarrier F hsource r).carrier :=
    orderThreeAffinePuncturedAction_free F hsource r
  let _ : ContinuousConstSMul (FiniteCyclic 3)
      (orderThreeAffinePuncturedCarrier F hsource r).carrier :=
    ⟨fun g ↦ (orderThreeAffinePuncturedAction_contMDiff
      F hprojectionSmooth hsource r g).continuous⟩
  let _ := orderThreeAffinePuncturedQuotientCharts F hprojectionSmooth hsource r
  let _ := regularFamilyDeckAction F
  have hsourceProjection :=
    (orderThreeAffinePuncturedQuotient_isManifold_and_projection_isLocalDiffeomorph
      F hprojectionSmooth hsource r).2
  let gauge := orderThreePuncturedCollarGaugeDiffeomorph F hprojectionAnalytic r
  have hcover : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (orderThreeCollarToRegular F hproper D ∘ gauge) := by
    intro q
    exact (gauge.isLocalDiffeomorph q).comp GlobalDeckTotalModel (RegularTotalSpace F)
      (hcollar (gauge q))
  apply quotientDescent_isLocalDiffeomorph
    (Quotient.mk (restrictedOrbitRel (orderThreeAffineFamilyAction F)
      (orderThreeAffinePuncturedCarrier F hsource r)))
    (Quotient.mk (MulAction.orbitRel Delta (RegularTotalSpace F)))
    (orderThreeCollarToRegular F hproper D ∘ gauge)
    (orderThreeAffineCollarToPuncturedGlobalFamily
      F hprojectionAnalytic hproper hsource D)
    hsourceProjection htarget hcover
  · funext q
    exact orderThreeAffineCollarToPuncturedGlobalFamily_mk
      F hprojectionAnalytic hproper hsource D q
  · exact Quotient.mk_surjective

/-- The order-four logarithmically gauged affine collar map is likewise locally
biholomorphic. -/
public theorem orderFourAffineCollarToPuncturedGlobalFamily_isLocalDiffeomorph_of_projections
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap F))]
    [T2Space (TotalSpace (parameterMap F))]
    [LocallyCompactSpace (TotalSpace (parameterMap F))]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (RegularTotalSpace F)]
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (PuncturedGlobalFamily F)]
    (hprojectionAnalytic : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F)))
    (hprojectionSmooth : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (projection (parameterMap F)))
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hsource : U.sourceAction = fuchsianSourceAction)
    (D : OrderFourLinearCollarSourceData (U := U) r)
    (hcollar : letI := regularBaseChartedSpace hproper
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (orderFourCollarToRegular F hproper D))
    (htarget : letI := regularFamilyDeckAction F
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
        (Quotient.mk (MulAction.orbitRel Delta (RegularTotalSpace F)))) :
    letI := orderFourAffinePuncturedQuotientCharts F hprojectionSmooth hsource r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (orderFourAffineCollarToPuncturedGlobalFamily
        F hprojectionAnalytic hproper hsource D) := by
  let _ := regularBaseChartedSpace hproper
  let _ := restrictedMulAction (orderFourAffineFamilyAction F)
    (orderFourAffinePuncturedCarrier F hsource r)
  let _ : IsCancelSMul (FiniteCyclic 4)
      (orderFourAffinePuncturedCarrier F hsource r).carrier :=
    orderFourAffinePuncturedAction_free F hsource r
  let _ : ContinuousConstSMul (FiniteCyclic 4)
      (orderFourAffinePuncturedCarrier F hsource r).carrier :=
    ⟨fun g ↦ (orderFourAffinePuncturedAction_contMDiff
      F hprojectionSmooth hsource r g).continuous⟩
  let _ := orderFourAffinePuncturedQuotientCharts F hprojectionSmooth hsource r
  let _ := regularFamilyDeckAction F
  have hsourceProjection :=
    (orderFourAffinePuncturedQuotient_isManifold_and_projection_isLocalDiffeomorph
      F hprojectionSmooth hsource r).2
  let gauge := orderFourPuncturedCollarGaugeDiffeomorph F hprojectionAnalytic r
  have hcover : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (orderFourCollarToRegular F hproper D ∘ gauge) := by
    intro q
    exact (gauge.isLocalDiffeomorph q).comp GlobalDeckTotalModel (RegularTotalSpace F)
      (hcollar (gauge q))
  apply quotientDescent_isLocalDiffeomorph
    (Quotient.mk (restrictedOrbitRel (orderFourAffineFamilyAction F)
      (orderFourAffinePuncturedCarrier F hsource r)))
    (Quotient.mk (MulAction.orbitRel Delta (RegularTotalSpace F)))
    (orderFourCollarToRegular F hproper D ∘ gauge)
    (orderFourAffineCollarToPuncturedGlobalFamily
      F hprojectionAnalytic hproper hsource D)
    hsourceProjection htarget hcover
  · funext q
    exact orderFourAffineCollarToPuncturedGlobalFamily_mk
      F hprojectionAnalytic hproper hsource D q
  · exact Quotient.mk_surjective

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
