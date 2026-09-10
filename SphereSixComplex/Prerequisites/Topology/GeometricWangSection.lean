module

public import SphereSixComplex.Prerequisites.Topology.WangHomologySplitting

@[expose] public section
noncomputable section
namespace SphereSixComplex

namespace WangHomologyPresentation

variable {HighRelations High Total LowRelations Low : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low]

/-- A specified geometric lift of the invariant classes in a Wang presentation. -/
public structure Section
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low) where
  lift : P.invariants →ₗ[ℤ] Total
  right_inv : P.totalToInvariants.comp lift = LinearMap.id

namespace Section

/-- Choose a section of the Wang boundary when its invariant term is projective. -/
public noncomputable def ofProjective
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    [Module.Projective ℤ P.invariants] : P.Section := by
  let lifting := Module.projective_lifting_property P.totalToInvariants LinearMap.id
    P.totalToInvariants_surjective
  exact
    { lift := Classical.choose lifting
      right_inv := Classical.choose_spec lifting }

end Section

/-- Split a Wang presentation using a specified geometric section. -/
public noncomputable def linearEquivOfSection
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.Section) :
    Total ≃ₗ[ℤ] P.Coinvariants × P.invariants := by
  let i := P.coinvariantsToTotal
  let p := P.totalToInvariants
  let s := S.lift
  let residual : Total →ₗ[ℤ] Total := LinearMap.id - s.comp p
  have hresidual (x : Total) : residual x ∈ LinearMap.range i := by
    apply (P.exact_coinvariantsToTotal_totalToInvariants (residual x)).mp
    have hsx := DFunLike.congr_fun S.right_inv (p x)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hsx
    change p (x - s (p x)) = 0
    rw [map_sub, hsx, sub_self]
  let residualRange : Total →ₗ[ℤ] LinearMap.range i :=
    residual.codRestrict (LinearMap.range i) hresidual
  let iEquivRange : P.Coinvariants ≃ₗ[ℤ] LinearMap.range i :=
    LinearEquiv.ofInjective i P.coinvariantsToTotal_injective
  let r : Total →ₗ[ℤ] P.Coinvariants := iEquivRange.symm.toLinearMap.comp residualRange
  let forward : Total →ₗ[ℤ] P.Coinvariants × P.invariants := r.prod p
  let inverse : P.Coinvariants × P.invariants →ₗ[ℤ] Total := LinearMap.coprod i s
  refine LinearEquiv.ofLinearMap forward inverse ?_ ?_
  · apply LinearMap.ext
    rintro ⟨y, z⟩
    have hpi (y : P.Coinvariants) : p (i y) = 0 :=
      P.exact_coinvariantsToTotal_totalToInvariants.apply_apply_eq_zero y
    have hps (y : P.invariants) : p (s y) = y := by
      have hsy := DFunLike.congr_fun S.right_inv y
      simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] using hsy
    have hr : r (i y + s z) = y := by
      apply iEquivRange.injective
      apply Subtype.ext
      change i (r (i y + s z)) = i y
      have hir : i (r (i y + s z)) = residual (i y + s z) := by
        change i (iEquivRange.symm (residualRange (i y + s z))) = residual (i y + s z)
        exact congrArg Subtype.val
          (iEquivRange.apply_symm_apply (residualRange (i y + s z)))
      rw [hir]
      change i y + s z - s (p (i y + s z)) = i y
      rw [map_add, hpi, hps, map_add, map_zero, zero_add]
      abel
    apply Prod.ext
    · exact hr
    · change p (i y + s z) = z
      rw [map_add, hpi, hps, zero_add]
  · apply LinearMap.ext
    intro x
    have hi : i (r x) = residual x := by
      change i (iEquivRange.symm (residualRange x)) = residual x
      exact congrArg Subtype.val (iEquivRange.apply_symm_apply (residualRange x))
    simp only [LinearMap.comp_apply]
    change i (r x) + s (p x) = x
    rw [hi]
    change x - s (p x) + s (p x) = x
    abel

end WangHomologyPresentation

end SphereSixComplex
end
end
