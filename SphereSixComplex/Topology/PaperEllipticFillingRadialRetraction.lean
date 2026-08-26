module

public import SphereSixComplex.Geometry.EllipticActualActionTopology
public import SphereSixComplex.Geometry.PaperAnalyticFillingPieces
public import SphereSixComplex.Topology.MayerVietoris

/-!
# Radial topology of the elliptic filling models

The fixed-product elliptic filling retracts equivariantly onto its central fibre.  This file
performs the radial contraction before taking the finite cyclic quotient, descends it, and records
the exact additional equivariant identification needed to transport the result to a varying
period-torus filling.
-/

open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap

namespace SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction

open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticActualActionTopology
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup

noncomputable section

/-- Linear contraction of the complex unit disc to its centre. -/
@[expose] public def discRadialHomotopy
    (p : unitInterval × ComplexUnitDisc) : ComplexUnitDisc :=
  ⟨((1 - (p.1 : ℝ) : ℝ) : ℂ) * p.2.1, by
    have hs0 : 0 ≤ 1 - (p.1 : ℝ) := sub_nonneg.mpr p.1.2.2
    have hs1 : 1 - (p.1 : ℝ) ≤ 1 := by linarith [p.1.2.1]
    have hnorm : ‖((1 - (p.1 : ℝ) : ℝ) : ℂ)‖ = 1 - (p.1 : ℝ) := by
      rw [Complex.norm_real, Real.norm_of_nonneg hs0]
    calc
      ‖(((1 - (p.1 : ℝ) : ℝ) : ℂ) * p.2.1)‖ =
          (1 - (p.1 : ℝ)) * ‖p.2.1‖ := by rw [norm_mul, hnorm]
      _ ≤ 1 * ‖p.2.1‖ := mul_le_mul_of_nonneg_right hs1 (norm_nonneg _)
      _ < 1 := by simpa using p.2.2⟩

public theorem discRadialHomotopy_continuous : Continuous discRadialHomotopy := by
  apply Continuous.subtype_mk
  exact ((Complex.continuous_ofReal.comp (continuous_const.sub
    (continuous_subtype_val.comp continuous_fst))).mul
      (continuous_subtype_val.comp continuous_snd))

@[simp]
public theorem discRadialHomotopy_zero (w : ComplexUnitDisc) :
    discRadialHomotopy (0, w) = w := by
  apply Subtype.ext
  simp [discRadialHomotopy]

@[simp]
public theorem discRadialHomotopy_one (w : ComplexUnitDisc) :
    discRadialHomotopy (1, w) = discCenter := by
  apply Subtype.ext
  simp [discRadialHomotopy, discCenter]

@[simp]
public theorem discRadialHomotopy_center (s : unitInterval) :
    discRadialHomotopy (s, discCenter) = discCenter := by
  apply Subtype.ext
  simp [discRadialHomotopy, discCenter]

public theorem discRadialHomotopy_discScalarEquiv_pow
    (lambda : ℂ) (hlambda : ‖lambda‖ = 1) (k : ℕ)
    (s : unitInterval) (w : ComplexUnitDisc) :
    discRadialHomotopy (s, (discScalarEquiv lambda hlambda ^ k) w) =
      (discScalarEquiv lambda hlambda ^ k) (discRadialHomotopy (s, w)) := by
  apply Subtype.ext
  change (((1 - (s : ℝ) : ℝ) : ℂ) *
      ((discScalarEquiv lambda hlambda ^ k) w).1) =
    ((discScalarEquiv lambda hlambda ^ k) (discRadialHomotopy (s, w))).1
  rw [discScalarEquiv_pow_apply_val, discScalarEquiv_pow_apply_val]
  change (((1 - (s : ℝ) : ℝ) : ℂ) * (lambda ^ k * w.1)) =
    lambda ^ k * (((1 - (s : ℝ) : ℝ) : ℂ) * w.1)
  ring

/-- Radius-`r` ball in a fixed disc--torus product. -/
public abbrev RadialProductBall (r : ℝ) (T : Type) [TopologicalSpace T] :=
  {p : ComplexUnitDisc × T // ‖(p.1 : ℂ)‖ < r}

/-- Positive radial rescaling identifies a radius-`r` product ball with the full unit-disc
product. -/
@[expose] public def radialProductBallHomeomorph
    {T : Type} [TopologicalSpace T] {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    RadialProductBall r T ≃ₜ ComplexUnitDisc × T where
  toFun p :=
    (⟨p.1.1.1 / (r : ℂ), by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
      exact (div_lt_one hr).mpr p.2⟩, p.1.2)
  invFun p :=
    ⟨(⟨(r : ℂ) * p.1.1, by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
      have h := mul_lt_mul_of_pos_left p.1.2 hr
      have h' : r * ‖p.1.1‖ < r := by simpa using h
      exact h'.trans hr1⟩, p.2), by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le]
      simpa using mul_lt_mul_of_pos_left p.1.2 hr⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp
    · rfl
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp
    · rfl
  continuous_toFun :=
    (Continuous.subtype_mk
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).div_const _)
      _).prodMk (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := Continuous.subtype_mk
    ((Continuous.subtype_mk
      (continuous_const.mul (continuous_subtype_val.comp continuous_fst)) _).prodMk
        continuous_snd) _

/-- A diagonal finite-cyclic action for which the radial contraction is equivariant. -/
public structure RadialEllipticActionData
    (m : ℕ) [NeZero m] (T : Type) [TopologicalSpace T] [AddCommGroup T] where
  actionData : EllipticActionData m ComplexUnitDisc T
  center_eq : actionData.center = discCenter
  representation_continuous : ∀ g : FiniteCyclic m,
    Continuous (actionData.representation g)
  radial_equivariant : ∀ (g : FiniteCyclic m) (s : unitInterval)
    (p : ComplexUnitDisc × T),
    (discRadialHomotopy
        (s, (actionMap actionData.diagonalAction g p).1),
      (actionMap actionData.diagonalAction g p).2) =
      actionMap actionData.diagonalAction g
        (discRadialHomotopy (s, p.1), p.2)

/-- Scalar disc rotation is exactly the condition needed for radial equivariance of the diagonal
finite-cyclic action. -/
@[expose] public def radialEllipticActionDataOfScalarRotation
    {m : ℕ} [NeZero m] {T : Type} [TopologicalSpace T] [AddCommGroup T]
    (D : EllipticActionData m ComplexUnitDisc T) (lambda : ℂ)
    (hlambda : ‖lambda‖ = 1)
    (hrotation : D.rotation = discScalarEquiv lambda hlambda)
    (hcenter : D.center = discCenter)
    (hcontinuous : ∀ g : FiniteCyclic m, Continuous (D.representation g)) :
    RadialEllipticActionData m T where
  actionData := D
  center_eq := hcenter
  representation_continuous := hcontinuous
  radial_equivariant := by
    intro g s p
    change (discRadialHomotopy (s, (D.representation g p).1),
        (D.representation g p).2) =
      D.representation g (discRadialHomotopy (s, p.1), p.2)
    rw [cyclic_eq_generator_pow g, map_pow,
      D.representation_generator]
    change (discRadialHomotopy
        (s, ((D.diagonalGenerator ^ (Multiplicative.toAdd g).val) p).1),
      ((D.diagonalGenerator ^ (Multiplicative.toAdd g).val) p).2) =
      (D.diagonalGenerator ^ (Multiplicative.toAdd g).val)
        (discRadialHomotopy (s, p.1), p.2)
    rw [D.diagonalGenerator_pow_apply, D.diagonalGenerator_pow_apply]
    apply Prod.ext
    · change discRadialHomotopy
          (s, (D.rotation ^ (Multiplicative.toAdd g).val) p.1) =
        (D.rotation ^ (Multiplicative.toAdd g).val)
          (discRadialHomotopy (s, p.1))
      rw [hrotation]
      exact discRadialHomotopy_discScalarEquiv_pow lambda hlambda _ s p.1
    · rfl

namespace RadialEllipticActionData

variable {m : ℕ} [NeZero m] {T : Type} [TopologicalSpace T] [AddCommGroup T]
    (D : RadialEllipticActionData m T)

public abbrev Product (_D : RadialEllipticActionData m T) := ComplexUnitDisc × T

public abbrev FillingQuotient :=
  Quotient (orbitRelOf D.actionData.diagonalAction)

/-- The central slice before taking the cyclic quotient. -/
@[expose] public def centralSlice : Set D.Product := {p | p.1 = discCenter}

/-- Retraction of the fixed product to the central slice. -/
@[expose] public def retract : C(D.Product, D.Product) where
  toFun p := (discCenter, p.2)
  continuous_toFun := continuous_const.prodMk continuous_snd

/-- The radial strong deformation homotopy on the fixed product. -/
@[expose] public def homotopy :
    ContinuousMap.Homotopy (ContinuousMap.id D.Product) D.retract where
  toFun p := (discRadialHomotopy (p.1, p.2.1), p.2.2)
  continuous_toFun := discRadialHomotopy_continuous.comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)) |>.prodMk
    (continuous_snd.comp continuous_snd)
  map_zero_left p := by simp
  map_one_left p := by simp [retract]

public theorem retract_mem (p : D.Product) : D.retract p ∈ D.centralSlice := by
  change discCenter = discCenter
  rfl

public theorem retract_fixed (p : D.Product) (hp : p ∈ D.centralSlice) :
    D.retract p = p := by
  rcases p with ⟨w, x⟩
  change w = discCenter at hp
  subst w
  rfl

public theorem homotopy_fixed (s : unitInterval) (p : D.Product)
    (hp : p ∈ D.centralSlice) : D.homotopy (s, p) = p := by
  rcases p with ⟨w, x⟩
  change w = discCenter at hp
  subst w
  change (discRadialHomotopy (s, discCenter), x) = (discCenter, x)
  rw [discRadialHomotopy_center]

public theorem retract_equivariant (g : FiniteCyclic m) (p : D.Product) :
    D.retract (actionMap D.actionData.diagonalAction g p) =
      actionMap D.actionData.diagonalAction g (D.retract p) := by
  have h := D.radial_equivariant g 1 p
  simpa [retract] using h

public theorem homotopy_equivariant (g : FiniteCyclic m) (s : unitInterval)
    (p : D.Product) :
    D.homotopy (s, actionMap D.actionData.diagonalAction g p) =
      actionMap D.actionData.diagonalAction g (D.homotopy (s, p)) := by
  exact D.radial_equivariant g s p

/-- The cyclic filling quotient is Hausdorff.  A finite group acts properly discontinuously, and
the disc times a locally compact Hausdorff fibre is locally compact Hausdorff, so the orbit
quotient is Hausdorff. -/
public theorem fillingQuotient_t2Space [T2Space T] [LocallyCompactSpace T] :
    T2Space D.FillingQuotient := by
  let _ := D.actionData.diagonalAction
  let _ : LocallyCompactSpace ComplexUnitDisc :=
    (isOpen_lt continuous_norm continuous_const).locallyCompactSpace
  let _ : ContinuousConstSMul (FiniteCyclic m) (ComplexUnitDisc × T) :=
    ⟨fun g => D.representation_continuous g⟩
  exact inferInstanceAs (T2Space (Quotient (MulAction.orbitRel _ _)))

/-- The image of the central slice in the orbit quotient: the reduced central bielliptic fibre. -/
@[expose] public def reducedCentralFiber : Set D.FillingQuotient :=
  Quotient.mk (orbitRelOf D.actionData.diagonalAction) '' D.centralSlice

/-- The radial retraction descended to the finite cyclic quotient. -/
@[expose] public def quotientRetract : C(D.FillingQuotient, D.FillingQuotient) := by
  exact {
    toFun := Quotient.lift
      (fun p ↦ Quotient.mk (orbitRelOf D.actionData.diagonalAction) (D.retract p)) (by
      intro a b hab
      apply Quotient.sound
      change orbitRelOf D.actionData.diagonalAction a b at hab
      change orbitRelOf D.actionData.diagonalAction (D.retract a) (D.retract b)
      change (∃ g : FiniteCyclic m,
        actionMap D.actionData.diagonalAction g b = a) at hab
      change ∃ g : FiniteCyclic m,
        actionMap D.actionData.diagonalAction g (D.retract b) = D.retract a
      obtain ⟨g, hg⟩ := hab
      refine ⟨g, ?_⟩
      rw [← hg]
      exact (D.retract_equivariant g b).symm)
    continuous_toFun := continuous_quot_lift _
      (continuous_quot_mk.comp D.retract.continuous) }

@[simp]
public theorem quotientRetract_mk (p : D.Product) :
    D.quotientRetract (Quotient.mk _ p) = Quotient.mk _ (D.retract p) := rfl

/-- The underlying descended radial homotopy. -/
@[expose] public def quotientHomotopyToFun :
    unitInterval × D.FillingQuotient → D.FillingQuotient := by
  exact fun z ↦ Quotient.lift
    (fun p ↦ Quotient.mk (orbitRelOf D.actionData.diagonalAction)
      (D.homotopy (z.1, p))) (by
      intro a b hab
      apply Quotient.sound
      change orbitRelOf D.actionData.diagonalAction a b at hab
      change orbitRelOf D.actionData.diagonalAction
        (D.homotopy (z.1, a)) (D.homotopy (z.1, b))
      change (∃ g : FiniteCyclic m,
        actionMap D.actionData.diagonalAction g b = a) at hab
      change ∃ g : FiniteCyclic m,
        actionMap D.actionData.diagonalAction g (D.homotopy (z.1, b)) =
          D.homotopy (z.1, a)
      obtain ⟨g, hg⟩ := hab
      refine ⟨g, ?_⟩
      rw [← hg]
      exact (D.homotopy_equivariant g z.1 b).symm) z.2

@[simp]
public theorem quotientHomotopyToFun_mk (s : unitInterval) (p : D.Product) :
    D.quotientHomotopyToFun (s, Quotient.mk _ p) =
      Quotient.mk _ (D.homotopy (s, p)) := rfl

public theorem quotientHomotopyToFun_continuous :
    Continuous D.quotientHomotopyToFun := by
  let _ := D.actionData.diagonalAction
  let _ : ContinuousConstSMul (FiniteCyclic m) D.Product :=
    ⟨D.representation_continuous⟩
  let q : D.Product → D.FillingQuotient :=
    Quotient.mk (orbitRelOf D.actionData.diagonalAction)
  have hq : IsOpenQuotientMap (Prod.map (id : unitInterval → unitInterval) q) :=
    IsOpenQuotientMap.id.prodMap
      (MulAction.isOpenQuotientMap_quotientMk
        (Γ := FiniteCyclic m) (T := D.Product))
  apply hq.isQuotientMap.continuous_iff.mpr
  rw [show D.quotientHomotopyToFun ∘ Prod.map id q =
      fun z : unitInterval × D.Product ↦
        Quotient.mk (orbitRelOf D.actionData.diagonalAction)
          (D.homotopy (z.1, z.2)) by
    funext z
    exact D.quotientHomotopyToFun_mk z.1 z.2]
  exact continuous_quot_mk.comp D.homotopy.continuous

/-- The strong deformation homotopy descended to the orbit quotient. -/
@[expose] public def quotientHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id D.FillingQuotient) D.quotientRetract where
  toFun := D.quotientHomotopyToFun
  continuous_toFun := D.quotientHomotopyToFun_continuous
  map_zero_left q := by
    induction q using Quotient.inductionOn with
    | _ p =>
      rw [D.quotientHomotopyToFun_mk]
      exact congrArg (Quotient.mk _) (D.homotopy.map_zero_left p)
  map_one_left q := by
    induction q using Quotient.inductionOn with
    | _ p =>
      rw [D.quotientHomotopyToFun_mk, D.quotientRetract_mk]
      exact congrArg (Quotient.mk _) (D.homotopy.map_one_left p)

public theorem quotientRetract_mem (q : D.FillingQuotient) :
    D.quotientRetract q ∈ D.reducedCentralFiber := by
  induction q using Quotient.inductionOn with
  | _ p => exact ⟨D.retract p, D.retract_mem p, D.quotientRetract_mk p |>.symm⟩

public theorem quotientRetract_fixed (q : D.FillingQuotient)
    (hq : q ∈ D.reducedCentralFiber) : D.quotientRetract q = q := by
  obtain ⟨p, hp, rfl⟩ := hq
  rw [D.quotientRetract_mk]
  exact congrArg (Quotient.mk _) (D.retract_fixed p hp)

public theorem quotientHomotopy_fixed (s : unitInterval) (q : D.FillingQuotient)
    (hq : q ∈ D.reducedCentralFiber) : D.quotientHomotopy (s, q) = q := by
  obtain ⟨p, hp, rfl⟩ := hq
  change D.quotientHomotopyToFun (s, Quotient.mk _ p) = Quotient.mk _ p
  rw [D.quotientHomotopyToFun_mk]
  exact congrArg (Quotient.mk _) (D.homotopy_fixed s p hp)

/-- The quotient retraction with codomain restricted to the reduced central fibre. -/
@[expose] public def centralRetraction :
    C(D.FillingQuotient, D.reducedCentralFiber) where
  toFun q := ⟨D.quotientRetract q, D.quotientRetract_mem q⟩
  continuous_toFun := D.quotientRetract.continuous.subtype_mk _

/-- Inclusion of the reduced central fibre into the quotient filling. -/
@[expose] public def centralInclusion :
    C(D.reducedCentralFiber, D.FillingQuotient) where
  toFun q := q.1
  continuous_toFun := continuous_subtype_val

/-- The quotient filling is homotopy equivalent to its reduced central bielliptic fibre. -/
@[expose] public def quotientHomotopyEquivCentralFiber :
    D.FillingQuotient ≃ₕ D.reducedCentralFiber where
  toFun := D.centralRetraction
  invFun := D.centralInclusion
  left_inv := ⟨D.quotientHomotopy.symm⟩
  right_inv := by
    rw [show D.centralRetraction.comp D.centralInclusion =
        ContinuousMap.id D.reducedCentralFiber by
      ext q
      exact D.quotientRetract_fixed q q.property]

/-- The descended retraction induces an isomorphism on integral singular homology. -/
public theorem quotientRetract_isIntegralHomologyEquivalence (k : ℕ) :
    IsIso (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
      (TopCat.ofHom D.quotientHomotopyEquivCentralFiber.toFun)) := by
  let F := (singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)
  let e := D.quotientHomotopyEquivCentralFiber
  let i : F.obj (TopCat.of D.FillingQuotient) ≅
      F.obj (TopCat.of D.reducedCentralFiber) :=
    CategoryTheory.Iso.mk (F.map (TopCat.ofHom e.toFun))
      (F.map (TopCat.ofHom e.invFun)) (by
        rw [← F.map_comp, ← F.map_id]
        exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
          e.left_inv.some (AddCommGrpCat.of ℤ) k) (by
        rw [← F.map_comp, ← F.map_id]
        exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
          e.right_inv.some (AddCommGrpCat.of ℤ) k)
  exact i.isIso_hom

end RadialEllipticActionData

/-- The concrete radial action on the actual order-three fixed period torus. -/
@[expose] public def orderThreeRadialActionData
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    RadialEllipticActionData 3
      (AdditiveTorus (parameterMap F U.zOne).1) :=
  radialEllipticActionDataOfScalarRotation
    (orderThreeActionData F) orderThreeMultiplier norm_orderThreeMultiplier rfl rfl
    (orderThreeRepresentation_continuous F)

/-- The concrete radial action on the actual order-four fixed period torus. -/
@[expose] public def orderFourRadialActionData
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    RadialEllipticActionData 4
      (AdditiveTorus (parameterMap F U.zTwo).1) :=
  radialEllipticActionDataOfScalarRotation
    (orderFourActionData F) orderFourMultiplier norm_orderFourMultiplier rfl rfl
    (orderFourRepresentation_continuous F)

/-- The actual fixed-product order-three filling retracts to its reduced central fibre. -/
public abbrev OrderThreeReducedCentralFiber
    {U : TriangleUniformization} (F : PeriodFunctions U) :=
  (orderThreeRadialActionData F).reducedCentralFiber

/-- The actual fixed-product order-four filling retracts to its reduced central fibre. -/
public abbrev OrderFourReducedCentralFiber
    {U : TriangleUniformization} (F : PeriodFunctions U) :=
  (orderFourRadialActionData F).reducedCentralFiber

/-- Order-three fixed-product filling, homotopy equivalent to the reduced bielliptic fibre. -/
@[expose] public def orderThreeFillingHomotopyEquivCentralFiber
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    (orderThreeRadialActionData F).FillingQuotient ≃ₕ
      OrderThreeReducedCentralFiber F :=
  (orderThreeRadialActionData F).quotientHomotopyEquivCentralFiber

/-- Order-four fixed-product filling, homotopy equivalent to the reduced bielliptic fibre. -/
@[expose] public def orderFourFillingHomotopyEquivCentralFiber
    {U : TriangleUniformization} (F : PeriodFunctions U) :
    (orderFourRadialActionData F).FillingQuotient ≃ₕ
      OrderFourReducedCentralFiber F :=
  (orderFourRadialActionData F).quotientHomotopyEquivCentralFiber

/-- Singular chains carry a space-level homotopy equivalence to a chain-homotopy equivalence. -/
@[expose] public def integralSingularChainHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) :
    HomotopyEquiv (SphereSixComplex.IntegralSingularChainComplex X)
      (SphereSixComplex.IntegralSingularChainComplex Y) where
  hom := SphereSixComplex.integralSingularChainMap e.toFun
  inv := SphereSixComplex.integralSingularChainMap e.invFun
  homotopyHomInvId := by
    let H : TopCat.Homotopy
        (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 (TopCat.of X)) :=
      e.left_inv.some
    simpa only [SphereSixComplex.integralSingularChainMap, Functor.map_comp] using
      (TopCat.Homotopy.singularChainComplexFunctorObjMap H
        (AddCommGrpCat.of ℤ)).trans (Homotopy.ofEq (by simp))
  homotopyInvHomId := by
    let H : TopCat.Homotopy
        (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 (TopCat.of Y)) :=
      e.right_inv.some
    simpa only [SphereSixComplex.integralSingularChainMap, Functor.map_comp] using
      (TopCat.Homotopy.singularChainComplexFunctorObjMap H
        (AddCommGrpCat.of ℤ)).trans (Homotopy.ofEq (by simp))

/-- Chain-level realization of the order-three radial retraction. -/
@[expose] public def orderThreeFillingSingularChainHomotopyEquiv
    {U : TriangleUniformization} (F : PeriodFunctions U) :=
  integralSingularChainHomotopyEquiv
    (orderThreeFillingHomotopyEquivCentralFiber F)

/-- Chain-level realization of the order-four radial retraction. -/
@[expose] public def orderFourFillingSingularChainHomotopyEquiv
    {U : TriangleUniformization} (F : PeriodFunctions U) :=
  integralSingularChainHomotopyEquiv
    (orderFourFillingHomotopyEquivCentralFiber F)

/-- An exact pre-quotient equivariant identification with a radial fixed-product filling.  This is
the topology input required to transport the radial retraction to a varying torus family. -/
public structure EquivariantRadialProductIdentification
    {m : ℕ} [NeZero m] {X T : Type} [TopologicalSpace X] [TopologicalSpace T]
    [AddCommGroup T] (sourceAction : MulAction (FiniteCyclic m) X)
    (D : RadialEllipticActionData m T) where
  toHomeomorph : X ≃ₜ D.Product
  equivariant : ∀ (g : FiniteCyclic m) (x : X),
    toHomeomorph (actionMap sourceAction g x) =
      actionMap D.actionData.diagonalAction g (toHomeomorph x)

namespace EquivariantRadialProductIdentification

variable {m : ℕ} [NeZero m] {X T : Type} [TopologicalSpace X] [TopologicalSpace T]
    [AddCommGroup T] {sourceAction : MulAction (FiniteCyclic m) X}
    {D : RadialEllipticActionData m T}
    (e : EquivariantRadialProductIdentification sourceAction D)

public abbrev SourceQuotient
    (_e : EquivariantRadialProductIdentification sourceAction D) :=
  Quotient (orbitRelOf sourceAction)

/-- The equivariant identification descends to the two orbit quotients. -/
@[expose] public def quotientHomeomorph : e.SourceQuotient ≃ₜ D.FillingQuotient :=
  Homeomorph.Quotient.congr e.toHomeomorph fun x y => by
    change (∃ g : FiniteCyclic m, actionMap sourceAction g y = x) ↔
      ∃ g : FiniteCyclic m,
        actionMap D.actionData.diagonalAction g (e.toHomeomorph y) = e.toHomeomorph x
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, (e.equivariant g y).symm.trans (congrArg e.toHomeomorph hg)⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, e.toHomeomorph.injective ((e.equivariant g y).trans hg)⟩

@[simp]
public theorem quotientHomeomorph_mk (x : X) :
    e.quotientHomeomorph (Quotient.mk _ x) =
      Quotient.mk _ (e.toHomeomorph x) := rfl

/-- Transported homotopy equivalence from the varying filling quotient to the fixed reduced
central bielliptic fibre. -/
@[expose] public def homotopyEquivCentralFiber :
    e.SourceQuotient ≃ₕ D.reducedCentralFiber :=
  e.quotientHomeomorph.toHomotopyEquiv.trans D.quotientHomotopyEquivCentralFiber

/-- Transported chain-homotopy equivalence on integral singular chains. -/
@[expose] public def singularChainHomotopyEquiv :=
  integralSingularChainHomotopyEquiv e.homotopyEquivCentralFiber

end EquivariantRadialProductIdentification

/-- An analytic whole-filling chart whose target is exactly a radial ball in a fixed product.
Unlike the earlier neighbourhood-only compatibility, the source here is the already restricted
varying filling, so `source_eq_univ` says that the chart covers the entire filling. -/
public structure RadialWholeFillingChart
    {m : ℕ} [NeZero m] (X : Type) [TopologicalSpace X]
    {T : Type} [TopologicalSpace T] [AddCommGroup T]
    (D : RadialEllipticActionData m T) (r : ℝ) where
  radius_pos : 0 < r
  radius_lt_one : r < 1
  gluing : OpenPartialHomeomorph X D.Product
  source_eq_univ : gluing.source = Set.univ
  target_eq_ball : gluing.target = {p | ‖(p.1 : ℂ)‖ < r}

namespace RadialWholeFillingChart

variable {m : ℕ} [NeZero m] {X T : Type} [TopologicalSpace X] [TopologicalSpace T]
    [AddCommGroup T] {D : RadialEllipticActionData m T} {r : ℝ}
    (C : RadialWholeFillingChart X D r)

/-- The whole-filling chart followed by radial rescaling is a genuine homeomorphism to the full
fixed product. -/
@[expose] public def toProductHomeomorph : X ≃ₜ D.Product :=
  (Homeomorph.Set.univ X).symm |>.trans
    (Homeomorph.setCongr C.source_eq_univ.symm) |>.trans
    C.gluing.toHomeomorphSourceTarget |>.trans
    (Homeomorph.setCongr C.target_eq_ball) |>.trans
    (radialProductBallHomeomorph C.radius_pos C.radius_lt_one)

end RadialWholeFillingChart

/-- Action-correct affine whole-filling compatibility.  The action is supplied explicitly so the
varying affine action cannot be confused with the unshifted family deck action. -/
public structure AffineRadialWholeFillingCompatibility
    {m : ℕ} [NeZero m] {X T : Type} [TopologicalSpace X] [TopologicalSpace T]
    [AddCommGroup T] (sourceAction : MulAction (FiniteCyclic m) X)
    (D : RadialEllipticActionData m T) (r : ℝ) where
  chart : RadialWholeFillingChart X D r
  equivariant : ∀ (g : FiniteCyclic m) (x : X),
    chart.toProductHomeomorph (actionMap sourceAction g x) =
      actionMap D.actionData.diagonalAction g (chart.toProductHomeomorph x)

namespace AffineRadialWholeFillingCompatibility

variable {m : ℕ} [NeZero m] {X T : Type} [TopologicalSpace X] [TopologicalSpace T]
    [AddCommGroup T] {sourceAction : MulAction (FiniteCyclic m) X}
    {D : RadialEllipticActionData m T} {r : ℝ}
    (C : AffineRadialWholeFillingCompatibility sourceAction D r)

/-- An affine radial whole-filling chart supplies exactly the pre-quotient identification used by
the quotient strong deformation retraction. -/
@[expose] public def toProductIdentification :
    EquivariantRadialProductIdentification sourceAction D where
  toHomeomorph := C.chart.toProductHomeomorph
  equivariant := C.equivariant

end AffineRadialWholeFillingCompatibility

variable (A : PaperAnalyticData) (r : ℝ)

/-- The missing exact topology bridge for the order-three varying filling. -/
public abbrev OrderThreeVaryingFillingProductIdentification :=
  EquivariantRadialProductIdentification (A.orderThreeFillingAction r)
    (orderThreeRadialActionData A.periods)

/-- The missing exact topology bridge for the order-four varying filling. -/
public abbrev OrderFourVaryingFillingProductIdentification :=
  EquivariantRadialProductIdentification (A.orderFourFillingAction r)
    (orderFourRadialActionData A.periods)

/-- Accurate affine radial whole-filling input for the actual order-three varying family. -/
public abbrev OrderThreeAffineRadialWholeFillingCompatibility :=
  AffineRadialWholeFillingCompatibility (A.orderThreeFillingAction r)
    (orderThreeRadialActionData A.periods) r

/-- Accurate affine radial whole-filling input for the actual order-four varying family. -/
public abbrev OrderFourAffineRadialWholeFillingCompatibility :=
  AffineRadialWholeFillingCompatibility (A.orderFourFillingAction r)
    (orderFourRadialActionData A.periods) r

/-- The accurate order-three affine whole-filling input instantiates the radial product contract. -/
@[expose] public def OrderThreeAffineRadialWholeFillingCompatibility.toVaryingFillingProductIdentification
    (C : OrderThreeAffineRadialWholeFillingCompatibility A r) :
    OrderThreeVaryingFillingProductIdentification A r :=
  C.toProductIdentification

/-- The accurate order-four affine whole-filling input instantiates the radial product contract. -/
@[expose] public def OrderFourAffineRadialWholeFillingCompatibility.toVaryingFillingProductIdentification
    (C : OrderFourAffineRadialWholeFillingCompatibility A r) :
    OrderFourVaryingFillingProductIdentification A r :=
  C.toProductIdentification

/-- The exact order-three varying-filling conclusion obtained from the equivariant product
identification. -/
@[expose] public def orderThreeVaryingFillingHomotopyEquivCentralFiber
    (e : OrderThreeVaryingFillingProductIdentification A r) :
    A.OrderThreeVaryingFilling r ≃ₕ OrderThreeReducedCentralFiber A.periods :=
  e.homotopyEquivCentralFiber

/-- The exact order-four varying-filling conclusion obtained from the equivariant product
identification. -/
@[expose] public def orderFourVaryingFillingHomotopyEquivCentralFiber
    (e : OrderFourVaryingFillingProductIdentification A r) :
    A.OrderFourVaryingFilling r ≃ₕ OrderFourReducedCentralFiber A.periods :=
  e.homotopyEquivCentralFiber

/-- Integral singular-chain realization of the transported order-three equivalence. -/
@[expose] public def orderThreeVaryingFillingSingularChainHomotopyEquiv
    (e : OrderThreeVaryingFillingProductIdentification A r) :=
  integralSingularChainHomotopyEquiv
    (orderThreeVaryingFillingHomotopyEquivCentralFiber A r e)

/-- Integral singular-chain realization of the transported order-four equivalence. -/
@[expose] public def orderFourVaryingFillingSingularChainHomotopyEquiv
    (e : OrderFourVaryingFillingProductIdentification A r) :=
  integralSingularChainHomotopyEquiv
    (orderFourVaryingFillingHomotopyEquivCentralFiber A r e)

/-- The action-correct order-three affine whole-filling chart yields the desired filling
homotopy equivalence; the conclusion is derived, not stored in the chart. -/
@[expose] public def orderThreeVaryingFillingHomotopyEquivCentralFiber_of_affineRadialChart
    (C : OrderThreeAffineRadialWholeFillingCompatibility A r) :
    A.OrderThreeVaryingFilling r ≃ₕ OrderThreeReducedCentralFiber A.periods :=
  orderThreeVaryingFillingHomotopyEquivCentralFiber A r
    C.toVaryingFillingProductIdentification

/-- The analogous order-four affine whole-filling conclusion. -/
@[expose] public def orderFourVaryingFillingHomotopyEquivCentralFiber_of_affineRadialChart
    (C : OrderFourAffineRadialWholeFillingCompatibility A r) :
    A.OrderFourVaryingFilling r ≃ₕ OrderFourReducedCentralFiber A.periods :=
  orderFourVaryingFillingHomotopyEquivCentralFiber A r
    C.toVaryingFillingProductIdentification

/-- Integral singular-chain realization derived from the order-three affine radial chart. -/
@[expose] public def orderThreeVaryingFillingSingularChainHomotopyEquiv_of_affineRadialChart
    (C : OrderThreeAffineRadialWholeFillingCompatibility A r) :=
  integralSingularChainHomotopyEquiv
    (orderThreeVaryingFillingHomotopyEquivCentralFiber_of_affineRadialChart A r C)

/-- Integral singular-chain realization derived from the order-four affine radial chart. -/
@[expose] public def orderFourVaryingFillingSingularChainHomotopyEquiv_of_affineRadialChart
    (C : OrderFourAffineRadialWholeFillingCompatibility A r) :=
  integralSingularChainHomotopyEquiv
    (orderFourVaryingFillingHomotopyEquivCentralFiber_of_affineRadialChart A r C)

end

end SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
