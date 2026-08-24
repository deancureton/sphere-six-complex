module

public import SphereSixComplex.Topology.RelativeSingularHomology
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# Collapsing the boundary of the seven-disk

This file constructs the topological quotient which collapses the boundary of a disk, identifies
its underlying point set with the one-point extension of the disk interior, and records the
standard homeomorphism from the one-point compactification of the open seven-ball to the
seven-sphere.

It also constructs the canonical chain map from relative singular chains of a pair to singular
chains of its collapse quotient modulo the collapsed basepoint.  The remaining comparison is the
excision assertion that this concrete map is a quasi-isomorphism; mathlib currently has no theorem
which proves it.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Function Metric Set Topology

namespace SphereSixComplex

section Collapse

variable {A X : TopCat} (i : A ⟶ X)

/-- The equivalence relation which identifies all points in the image of `i` and no others. -/
public def collapseSetoid : Setoid X where
  r x y := x = y ∨ (x ∈ Set.range i ∧ y ∈ Set.range i)
  iseqv := by
    refine ⟨fun x ↦ Or.inl rfl, ?_, ?_⟩
    · intro x y h
      exact h.elim (fun hxy ↦ Or.inl hxy.symm) fun hxy ↦ Or.inr ⟨hxy.2, hxy.1⟩
    · intro x y z hxy hyz
      rcases hxy with rfl | ⟨hx, hy⟩
      · exact hyz
      rcases hyz with rfl | ⟨_, hz⟩
      · exact Or.inr ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hz⟩

/-- The point-set quotient obtained by collapsing the image of `i`. -/
public abbrev CollapseQuotient := Quotient (collapseSetoid i)

/-- The collapse quotient as a categorical topological space, with the quotient topology. -/
public noncomputable def collapseQuotientObj : TopCat :=
  TopCat.of (CollapseQuotient i)

/-- The canonical quotient map which collapses the image of `i`. -/
public noncomputable def collapseQuotientMap : X ⟶ collapseQuotientObj i :=
  TopCat.ofHom ⟨@Quotient.mk' X (collapseSetoid i), continuous_quotient_mk'⟩

@[simp]
public theorem collapseQuotientMap_apply (x : X) :
    collapseQuotientMap i x = @Quotient.mk' X (collapseSetoid i) x :=
  rfl

/-- A chosen point of the collapsed subspace determines the distinguished quotient point. -/
public noncomputable def collapseQuotientBasepoint (a : A) :
    TopCat.of PUnit ⟶ collapseQuotientObj i :=
  TopCat.ofHom
    ⟨fun _ ↦ @Quotient.mk' X (collapseSetoid i) (i a), continuous_const⟩

/-- The unique map to the one-point space. -/
public noncomputable def collapseToPoint : A ⟶ TopCat.of PUnit :=
  TopCat.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩

/-- The quotient map is constant on the collapsed subspace. -/
public theorem collapseQuotientMap_comp_subspace (a : A) :
    i ≫ collapseQuotientMap i = collapseToPoint ≫ collapseQuotientBasepoint i a := by
  ext x
  change @Quotient.mk' X (collapseSetoid i) (i x) =
    @Quotient.mk' X (collapseSetoid i) (i a)
  apply Quotient.sound
  exact Or.inr ⟨⟨x, rfl⟩, ⟨a, rfl⟩⟩

/-- Points outside the collapsed image. -/
public abbrev CollapseComplement := {x : X // x ∉ Set.range i}

/-- The underlying point-set quotient is the one-point extension of the complement. -/
public noncomputable def collapseQuotientEquivOnePointComplement (a : A) :
    CollapseQuotient i ≃ OnePoint (CollapseComplement i) := by
  classical
  let f : X → OnePoint (CollapseComplement i) := fun x ↦
    dite (x ∈ Set.range i) (fun _ ↦ OnePoint.infty)
      (fun hx ↦ (⟨x, hx⟩ : CollapseComplement i))
  have hf : ∀ x y, collapseSetoid i x y → f x = f y := by
    intro x y hxy
    rcases hxy with rfl | ⟨hx, hy⟩
    · rfl
    · dsimp [f]
      rw [dif_pos hx, dif_pos hy]
  let g : OnePoint (CollapseComplement i) → CollapseQuotient i := fun p ↦
    p.elim (@Quotient.mk' X (collapseSetoid i) (i a))
      (fun x ↦ @Quotient.mk' X (collapseSetoid i) x.1)
  refine
    { toFun := Quotient.lift f hf
      invFun := g
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    refine Quotient.inductionOn q ?_
    intro x
    by_cases hx : x ∈ Set.range i
    · change g (f x) = @Quotient.mk' X (collapseSetoid i) x
      have hfx : f x = OnePoint.infty := by
        dsimp [f]
        rw [dif_pos hx]
      rw [hfx]
      change @Quotient.mk' X (collapseSetoid i) (i a) =
        @Quotient.mk' X (collapseSetoid i) x
      apply Quotient.sound
      exact Or.inr ⟨⟨a, rfl⟩, hx⟩
    · change g (f x) = @Quotient.mk' X (collapseSetoid i) x
      have hfx : f x = (↑(⟨x, hx⟩ : CollapseComplement i) :
          OnePoint (CollapseComplement i)) := by
        dsimp [f]
        rw [dif_neg hx]
      rw [hfx]
      rfl
  · intro p
    induction p using OnePoint.rec with
    | infty =>
        change Quotient.lift f hf (@Quotient.mk' X (collapseSetoid i) (i a)) = _
        change f (i a) = _
        dsimp [f]
        rw [dif_pos ⟨a, rfl⟩]
    | coe x =>
        change Quotient.lift f hf (@Quotient.mk' X (collapseSetoid i) x.1) = _
        change f x.1 = _
        dsimp [f]
        rw [dif_neg x.2]

/-- Reduced singular chains based at `b`, modeled as the cokernel of the singular chains of the
basepoint inclusion. -/
public noncomputable abbrev ReducedIntegralSingularChainComplex
    {Q : TopCat} (b : TopCat.of PUnit ⟶ Q) : ChainComplex AddCommGrpCat ℕ :=
  RelativeIntegralSingularChainComplex b

/-- The quotient singular-chain map followed by projection away from the collapsed basepoint. -/
public noncomputable def collapseAmbientToReducedChains (a : A) :
    IntegralSingularChainComplexObj X ⟶
      ReducedIntegralSingularChainComplex (collapseQuotientBasepoint i a) :=
  integralSingularChainMapObj (collapseQuotientMap i) ≫
    relativeIntegralSingularChainProjection (collapseQuotientBasepoint i a)

/-- The ambient-to-reduced map kills chains coming from the collapsed subspace. -/
public theorem collapseAmbientToReducedChains_comp_subspace (a : A) :
    integralSingularChainMapObj i ≫ collapseAmbientToReducedChains i a = 0 := by
  rw [collapseAmbientToReducedChains, ← Category.assoc]
  change
    (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map i ≫
      ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (collapseQuotientMap i)) ≫ _ = 0
  rw [← Functor.map_comp]
  rw [collapseQuotientMap_comp_subspace i a]
  rw [Functor.map_comp]
  change
    ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map collapseToPoint ≫
      (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (collapseQuotientBasepoint i a) ≫
        cokernel.π (((singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map (collapseQuotientBasepoint i a))) = 0
  rw [cokernel.condition]
  exact Limits.comp_zero

/-- The canonical chain map from relative chains to reduced chains of the collapse quotient. -/
public noncomputable def relativeChainsToReducedCollapseChains (a : A) :
    RelativeIntegralSingularChainComplex i ⟶
      ReducedIntegralSingularChainComplex (collapseQuotientBasepoint i a) :=
  cokernel.desc (integralSingularChainMapObj i)
    (collapseAmbientToReducedChains i a)
    (collapseAmbientToReducedChains_comp_subspace i a)

@[reassoc (attr := simp)]
public theorem relativeChainsToReducedCollapseChains_comp_projection (a : A) :
    relativeIntegralSingularChainProjection i ≫
      relativeChainsToReducedCollapseChains i a = collapseAmbientToReducedChains i a :=
  cokernel.π_desc _ _ _

end Collapse

section SevenDisk

/-- The quotient `D⁷/S⁶`. -/
public noncomputable abbrev DiskBoundaryQuotientSeven :=
  CollapseQuotient (TopCat.diskBoundaryInclusion.{0} 7)

/-- The topological quotient `D⁷/S⁶`. -/
public noncomputable abbrev DiskBoundaryQuotientSevenObj :=
  collapseQuotientObj (TopCat.diskBoundaryInclusion.{0} 7)

/-- The quotient map `D⁷ ⟶ D⁷/S⁶`. -/
public noncomputable abbrev diskBoundaryQuotientSevenMap :
    TopCat.disk.{0} 7 ⟶ DiskBoundaryQuotientSevenObj :=
  collapseQuotientMap (TopCat.diskBoundaryInclusion.{0} 7)

/-- The canonical disk-collapse map is a quotient map. -/
public theorem diskBoundaryQuotientSevenMap_isQuotientMap :
    IsQuotientMap diskBoundaryQuotientSevenMap :=
  isQuotientMap_quotient_mk'

/-- A concrete point on `S⁶ = ∂D⁷`. -/
public noncomputable def diskBoundarySevenBasepoint : TopCat.diskBoundary.{0} 7 := by
  let v : EuclideanSpace ℝ (Fin 7) := PiLp.single 2 (0 : Fin 7) 1
  exact ULift.up ⟨v, by simp [v]⟩

/-- The distinguished collapsed boundary point of `D⁷/S⁶`. -/
public noncomputable abbrev diskBoundaryQuotientSevenBasepoint :
    TopCat.of PUnit ⟶ DiskBoundaryQuotientSevenObj :=
  collapseQuotientBasepoint (TopCat.diskBoundaryInclusion.{0} 7) diskBoundarySevenBasepoint

/-- Every boundary point maps to the distinguished collapsed point. -/
@[simp]
public theorem diskBoundaryQuotientSevenMap_boundary (x : TopCat.diskBoundary.{0} 7) :
    diskBoundaryQuotientSevenMap ((TopCat.diskBoundaryInclusion.{0} 7) x) =
      diskBoundaryQuotientSevenBasepoint PUnit.unit := by
  apply Quotient.sound
  exact Or.inr ⟨⟨x, rfl⟩, ⟨diskBoundarySevenBasepoint, rfl⟩⟩

/-- The complement of the collapsed boundary inside the closed disk is homeomorphic to the open
ball. -/
public noncomputable def diskSevenComplementBoundaryEquivBall :
    CollapseComplement (TopCat.diskBoundaryInclusion.{0} 7) ≃
      (TopCat.ball.{0} 7 : Type) :=
    { toFun := fun x ↦
        ⟨x.1.down.1, by
          have hxclosed := x.1.down.2
          simp only [Metric.mem_closedBall, dist_zero_right] at hxclosed
          simpa only [Metric.mem_ball, dist_zero_right] using
            (lt_of_le_of_ne hxclosed fun h ↦ x.2
              ⟨ULift.up ⟨x.1.down.1, by
                simpa only [Metric.mem_sphere, dist_zero_right] using h⟩, rfl⟩)⟩
      invFun := fun x ↦
        ⟨ULift.up ⟨x.down.1, Metric.ball_subset_closedBall x.down.2⟩, by
          intro hx
          obtain ⟨y, hy⟩ := hx
          have heq : y.down.1 = x.down.1 := by
            exact congrArg (fun z : TopCat.disk.{0} 7 => z.down.1) hy
          have hnorm : ‖x.down.1‖ = 1 := by
            simpa only [Metric.mem_sphere, dist_zero_right, heq] using y.down.2
          have hlt : ‖x.down.1‖ < 1 := by
            simpa only [Metric.mem_ball, dist_zero_right] using x.down.2
          exact hlt.ne hnorm⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply ULift.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply ULift.ext
        apply Subtype.ext
        rfl }

/-- The preceding point-set equivalence is a homeomorphism. -/
public noncomputable def diskSevenComplementBoundaryHomeomorphBall :
    CollapseComplement (TopCat.diskBoundaryInclusion.{0} 7) ≃ₜ
      (TopCat.ball.{0} 7 : Type) where
  toEquiv := diskSevenComplementBoundaryEquivBall
  continuous_toFun := by
    dsimp only [diskSevenComplementBoundaryEquivBall]
    fun_prop
  continuous_invFun := by
    dsimp only [diskSevenComplementBoundaryEquivBall]
    fun_prop

/-- The one-point compactification of the open seven-ball is the standard seven-sphere. -/
public noncomputable def onePointBallSevenHomeomorphSphereSeven :
    OnePoint (TopCat.ball.{0} 7 : Type) ≃ₜ
      (TopCat.sphere.{0} 7 : Type) := by
  let euclideanToBall : EuclideanSpace ℝ (Fin 7) ≃ₜ (TopCat.ball.{0} 7 : Type) :=
    (Homeomorph.unitBall : EuclideanSpace ℝ (Fin 7) ≃ₜ
      Metric.ball (0 : EuclideanSpace ℝ (Fin 7)) 1) |>.trans Homeomorph.ulift.symm
  exact (euclideanToBall.symm.onePointCongr).trans <|
    (onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin 7)) (by simp)).trans
      Homeomorph.ulift.symm

/-- The explicit point-set equivalence `D⁷/S⁶ ≃ S⁷`.  The only unproved topological
property is continuity of its first factor from the quotient to the one-point compactification. -/
public noncomputable def diskBoundaryQuotientSevenEquivSphereSeven :
    DiskBoundaryQuotientSeven ≃ (TopCat.sphere.{0} 7 : Type) :=
  (collapseQuotientEquivOnePointComplement
      (TopCat.diskBoundaryInclusion.{0} 7) diskBoundarySevenBasepoint).trans
    ((diskSevenComplementBoundaryHomeomorphBall.onePointCongr.trans
      onePointBallSevenHomeomorphSphereSeven).toEquiv)

/-- The sphere point corresponding to the collapsed boundary. -/
public noncomputable def diskBoundaryQuotientSevenSphereBasepoint :
    TopCat.sphere.{0} 7 :=
  onePointBallSevenHomeomorphSphereSeven OnePoint.infty

/-- The exact geometric continuity statement absent from mathlib: the explicit quotient-to-one-
point-complement equivalence respects the quotient topology. -/
public def DiskBoundaryCollapseToOnePointContinuous : Prop :=
  Continuous (collapseQuotientEquivOnePointComplement
    (TopCat.diskBoundaryInclusion.{0} 7) diskBoundarySevenBasepoint)

/-- The precise quotient-topology statement needed to promote the point-set equivalence to a
homeomorphism. -/
public def DiskBoundaryQuotientSevenTopologyComparison : Prop :=
  Continuous diskBoundaryQuotientSevenEquivSphereSeven

/-- The topology comparison follows from continuity of the sole non-library factor. -/
public theorem diskBoundaryQuotientSevenTopologyComparison_of_collapseContinuous
    (h : DiskBoundaryCollapseToOnePointContinuous) :
    DiskBoundaryQuotientSevenTopologyComparison :=
  (diskSevenComplementBoundaryHomeomorphBall.onePointCongr.trans
    onePointBallSevenHomeomorphSphereSeven).continuous.comp h

/-- Continuity of the explicit equivalence gives the expected homeomorphism.  Its inverse is
automatic because the quotient is compact and the sphere is Hausdorff. -/
public noncomputable def diskBoundaryQuotientSevenHomeomorphSphereSeven
    (h : DiskBoundaryQuotientSevenTopologyComparison) :
    DiskBoundaryQuotientSeven ≃ₜ (TopCat.sphere.{0} 7 : Type) := by
  letI : T2Space (TopCat.sphere.{0} 7 : Type) :=
    Homeomorph.ulift.symm.t2Space
  exact h.homeoOfEquivCompactToT2

/-- The canonical relative-to-reduced chain comparison for the pair `(D⁷,S⁶)`. -/
public noncomputable abbrev diskSevenRelativeChainsToReducedQuotientChains :
    DiskSevenSphereSixRelativeIntegralSingularChainComplex ⟶
      ReducedIntegralSingularChainComplex diskBoundaryQuotientSevenBasepoint :=
  relativeChainsToReducedCollapseChains
    (TopCat.diskBoundaryInclusion.{0} 7) diskBoundarySevenBasepoint

/-- The exact missing excision statement: the canonical chain map from relative chains of
`(D⁷,S⁶)` to reduced chains of `D⁷/S⁶` induces homology isomorphisms. -/
public def DiskSevenRelativeQuotientExcision : Prop :=
  ∀ n : ℕ,
    IsIso (HomologicalComplex.homologyMap
      diskSevenRelativeChainsToReducedQuotientChains n)

end SevenDisk

end SphereSixComplex
