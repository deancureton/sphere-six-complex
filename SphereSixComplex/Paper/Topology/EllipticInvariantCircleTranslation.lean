module
public import SphereSixComplex.Paper.Topology.PaperEllipticFillingRadialRetraction
public import SphereSixComplex.Paper.Topology.IntegerPeriodCircle

@[expose] public section
noncomputable section
open scoped ContinuousMap
namespace SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Geometry SphereSixComplex.TriangleGroup
open EllipticLocalCoordinates EquivariantQuotientHomeomorph
namespace RadialEllipticActionData
variable {m : ℕ} [NeZero m] {T : Type} [TopologicalSpace T] [AddCommGroup T]
  [IsTopologicalAddGroup T] (D : RadialEllipticActionData m T)
  (c : C(UnitAddCircle, T)) (hc : ∀ z, D.actionData.automorphism (c z) = c z)

public def circleTranslateProduct : C(UnitAddCircle × D.Product, D.Product) where
  toFun z := (z.2.1, c z.1 + z.2.2)
  continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
    ((c.continuous.comp continuous_fst).add (continuous_snd.comp continuous_snd))

include hc in
public theorem circleTranslateProduct_generator (z : UnitAddCircle) (p : D.Product) :
    D.actionData.diagonalGenerator (D.circleTranslateProduct c (z,p)) =
      D.circleTranslateProduct c (z,D.actionData.diagonalGenerator p) := by
  apply Prod.ext
  · rfl
  · change D.actionData.automorphism (c z + p.2) + D.actionData.translation =
      c z + (D.actionData.automorphism p.2 + D.actionData.translation)
    rw [map_add, hc, add_assoc]

include hc in
public theorem circleTranslateProduct_equivariant
    (g : FiniteCyclic m) (z : UnitAddCircle) (p : D.Product) :
    actionMap D.actionData.diagonalAction g (D.circleTranslateProduct c (z,p)) =
      D.circleTranslateProduct c (z, actionMap D.actionData.diagonalAction g p) := by
  change D.actionData.representation g _ = D.circleTranslateProduct c (z,D.actionData.representation g p)
  rw [cyclic_eq_generator_pow g, map_pow, D.actionData.representation_generator]
  generalize (Multiplicative.toAdd g).val = k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, D.circleTranslateProduct_generator c hc]
    rfl

public def circleTranslate : C(UnitAddCircle × D.FillingQuotient, D.FillingQuotient) where
  toFun z := Quotient.lift (fun p ↦ Quotient.mk (orbitRelOf D.actionData.diagonalAction) (D.circleTranslateProduct c (z.1,p)))
    (by
      intro a b hab
      obtain ⟨g,hg⟩ := hab
      apply Quotient.sound
      refine ⟨g, ?_⟩
      change actionMap D.actionData.diagonalAction g b = a at hg
      change actionMap D.actionData.diagonalAction g (D.circleTranslateProduct c (z.1,b)) = _
      rw [D.circleTranslateProduct_equivariant c hc, hg]) z.2
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact continuous_quot_mk.comp (D.circleTranslateProduct c).continuous

public theorem circleTranslate_mk (z : UnitAddCircle) (p : D.Product) :
    D.circleTranslate c hc (z,Quotient.mk _ p) = Quotient.mk _ (p.1,c z + p.2) := rfl

public theorem circleTranslate_reduced (z : UnitAddCircle) (p : D.reducedCentralFiber) :
    D.circleTranslate c hc (z,p.1) ∈ D.reducedCentralFiber := by
  obtain ⟨q,hq,hp⟩ := p.2
  rw [← hp, D.circleTranslate_mk]
  exact ⟨(q.1,c z + q.2), hq, rfl⟩

public def reducedCircleTranslate : C(UnitAddCircle × D.reducedCentralFiber, D.reducedCentralFiber) where
  toFun z := ⟨D.circleTranslate c hc (z.1,z.2.1), D.circleTranslate_reduced c hc z.1 z.2⟩
  continuous_toFun := ((D.circleTranslate c hc).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

end RadialEllipticActionData
end SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
