module

public import SphereSixComplex.Prerequisites.Topology.StandardTorusHomology
public import SphereSixComplex.Paper.Geometry.EllipticFamilySpecialization

@[expose] public section
noncomputable section
set_option linter.defProp false
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex
namespace StandardTorusHomology
section StandardTorusHomologyGroups
open CategoryTheory CategoryTheory.Limits

/-! ## The period torus in standard coordinates -/

section PeriodTorus

open Geometry Geometry.ComplexTorus Geometry.EllipticFamilySpecialization
open SphereSixComplex.Periods

variable (x : Parameters) (h : FullRank x)

/-- Real period coordinates modulo the standard integral lattice. -/
public def periodCoordMap (z : ComplexTwoSpace) : StdTorus 4 :=
  fun i ↦ ((h.realEquiv.symm z i : ℝ) : UnitAddCircle)

public theorem continuous_periodCoordMap : Continuous (periodCoordMap x h) :=
  continuous_pi fun i ↦
    (AddCircle.continuous_mk' 1).comp ((continuous_apply i).comp h.realEquiv.symm.continuous)

public theorem realEquiv_symm_periodVector (n : IntegerPeriods) :
    h.realEquiv.symm (periodVector x n) = integerToReal n := by
  apply h.realEquiv.injective
  rw [h.realEquiv.apply_symm_apply, h.map_integer]

public theorem periodCoordMap_eq_iff (z w : ComplexTwoSpace) :
    periodCoordMap x h z = periodCoordMap x h w ↔
      ∃ n : IntegerPeriods, z = periodVector x n + w := by
  constructor
  · intro hzw
    have hstep : ∀ i : Fin 4, ∃ k : ℤ,
        h.realEquiv.symm z i - h.realEquiv.symm w i = k := fun i ↦
      (unitAddCircle_eq_iff _ _).mp (congrFun hzw i)
    choose n hn using hstep
    refine ⟨n, ?_⟩
    have hreal : h.realEquiv.symm z = integerToReal n + h.realEquiv.symm w := by
      funext i
      have := hn i
      change h.realEquiv.symm z i = (n i : ℝ) + h.realEquiv.symm w i
      linarith [hn i]
    have := congrArg h.realEquiv hreal
    rw [h.realEquiv.apply_symm_apply, map_add, h.realEquiv.apply_symm_apply,
      h.map_integer] at this
    exact this
  · rintro ⟨n, rfl⟩
    funext i
    have hreal : h.realEquiv.symm (periodVector x n + w) =
        integerToReal n + h.realEquiv.symm w := by
      rw [map_add, realEquiv_symm_periodVector]
    change ((h.realEquiv.symm (periodVector x n + w) i : ℝ) : UnitAddCircle) = _
    rw [hreal]
    refine (unitAddCircle_eq_iff _ _).mpr ⟨n i, ?_⟩
    change (n i : ℝ) + h.realEquiv.symm w i - h.realEquiv.symm w i = (n i : ℝ)
    ring

public theorem periodCoordMap_orbitRel (z w : ComplexTwoSpace) :
    MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace z w ↔
      periodCoordMap x h z = periodCoordMap x h w := by
  rw [periodCoordMap_eq_iff, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨n, hn⟩ := g.toAdd.2
    refine ⟨n, ?_⟩
    have hn' : periodVector x n = (g.toAdd : ComplexTwoSpace) := hn
    rw [hn']
    exact hg.symm
  · rintro ⟨n, hn⟩
    exact ⟨Multiplicative.ofAdd ⟨periodVector x n, ⟨n, rfl⟩⟩, hn.symm⟩

/-- Standard real coordinates on a full-rank period torus. -/
public def additiveTorusStdMap : AdditiveTorus x → StdTorus 4 :=
  Quotient.lift (periodCoordMap x h) fun z w hzw ↦ (periodCoordMap_orbitRel x h z w).mp hzw

public theorem additiveTorusStdMap_injective : Function.Injective (additiveTorusStdMap x h) := by
  refine fun a b ↦ Quotient.inductionOn₂ a b fun z w hzw ↦ ?_
  exact Quotient.sound ((periodCoordMap_orbitRel x h z w).mpr hzw)

public theorem additiveTorusStdMap_surjective : Function.Surjective (additiveTorusStdMap x h) := by
  intro c
  have hstep : ∀ i : Fin 4, ∃ r : ℝ, ((r : ℝ) : UnitAddCircle) = c i := fun i ↦
    QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℝ)) (c i)
  choose r hr using hstep
  refine ⟨Quotient.mk _ (h.realEquiv r), ?_⟩
  show periodCoordMap x h (h.realEquiv r) = c
  funext i
  change ((h.realEquiv.symm (h.realEquiv r) i : ℝ) : UnitAddCircle) = c i
  rw [h.realEquiv.symm_apply_apply]
  exact hr i

/-- A full-rank period torus is the standard real four-torus. -/
public def additiveTorusStdHomeomorph : AdditiveTorus x ≃ₜ StdTorus 4 :=
  haveI := torus_compactSpace x h
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (additiveTorusStdMap x h)
      ⟨additiveTorusStdMap_injective x h, additiveTorusStdMap_surjective x h⟩)
    (continuous_quot_lift _ (continuous_periodCoordMap x h))

@[simp]
public theorem additiveTorusStdHomeomorph_apply (q : AdditiveTorus x) :
    additiveTorusStdHomeomorph x h q = additiveTorusStdMap x h q := rfl

end PeriodTorus

/-! ## The standard integral bases of a full-rank period torus -/

section Bases

open Geometry Geometry.ComplexTorus Geometry.EllipticFamilySpecialization
open SphereSixComplex.Periods

private theorem integralSingularHomologyEquiv_eq_map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (k : ℕ) (e : X ≃ₜ Y) (z : IntegralSingularHomology k X) :
    integralSingularHomologyEquiv k e z =
      integralSingularHomologyMap k (e : C(X, Y)) z := rfl

/-- The standard integral degree-one basis of a full-rank period torus. -/
public def additiveTorusHomologyDegreeOne (x : Parameters) (h : FullRank x) :
    IntegralSingularHomology 1 (AdditiveTorus x) ≃+ (Fin 4 → ℤ) :=
  (integralSingularHomologyEquiv 1 (additiveTorusStdHomeomorph x h)).trans
    stdTorusFourHomologyOne

private theorem additiveTorusHomologyDegreeOne_apply (x : Parameters) (h : FullRank x)
    (z : IntegralSingularHomology 1 (AdditiveTorus x)) :
    additiveTorusHomologyDegreeOne x h z =
      stdTorusFourHomologyOne
        (integralSingularHomologyEquiv 1 (additiveTorusStdHomeomorph x h) z) := rfl

/-- The standard integral degree-two basis of a full-rank period torus. -/
public def additiveTorusHomologyDegreeTwo (x : Parameters) (h : FullRank x) :
    IntegralSingularHomology 2 (AdditiveTorus x) ≃+ (Fin 6 → ℤ) :=
  (integralSingularHomologyEquiv 2 (additiveTorusStdHomeomorph x h)).trans
    stdTorusFourHomologyTwo

private theorem additiveTorusHomologyDegreeTwo_apply (x : Parameters) (h : FullRank x)
    (z : IntegralSingularHomology 2 (AdditiveTorus x)) :
    additiveTorusHomologyDegreeTwo x h z =
      stdTorusFourHomologyTwo
        (integralSingularHomologyEquiv 2 (additiveTorusStdHomeomorph x h) z) := rfl

/-- Any homeomorphism of period tori covered by the real-coordinate identification is compatible
with the standard real coordinates. -/
private theorem additiveTorusStdHomeomorph_comp (x y : Parameters) (hx : FullRank x)
    (hy : FullRank y) (e : AdditiveTorus x ≃ₜ AdditiveTorus y)
    (he : ∀ z : ComplexTwoSpace,
      e (Quotient.mk _ z) = Quotient.mk _ (hy.realEquiv (hx.realEquiv.symm z)))
    (q : AdditiveTorus x) :
    additiveTorusStdHomeomorph y hy (e q) = additiveTorusStdHomeomorph x hx q := by
  rw [additiveTorusStdHomeomorph_apply, additiveTorusStdHomeomorph_apply]
  induction q using Quotient.inductionOn with
  | _ z =>
    rw [he z]
    show periodCoordMap y hy (hy.realEquiv (hx.realEquiv.symm z)) = periodCoordMap x hx z
    funext i
    change ((hy.realEquiv.symm (hy.realEquiv (hx.realEquiv.symm z)) i : ℝ) : UnitAddCircle) = _
    rw [hy.realEquiv.symm_apply_apply]
    rfl

private theorem additiveTorusStdHomeomorph_comp_continuousMap (x y : Parameters) (hx : FullRank x)
    (hy : FullRank y) (e : AdditiveTorus x ≃ₜ AdditiveTorus y)
    (he : ∀ z : ComplexTwoSpace,
      e (Quotient.mk _ z) = Quotient.mk _ (hy.realEquiv (hx.realEquiv.symm z))) :
    ((additiveTorusStdHomeomorph y hy : C(AdditiveTorus y, StdTorus 4)).comp
        (e : C(AdditiveTorus x, AdditiveTorus y))) =
      (additiveTorusStdHomeomorph x hx : C(AdditiveTorus x, StdTorus 4)) :=
  ContinuousMap.ext fun q ↦ additiveTorusStdHomeomorph_comp x y hx hy e he q

/-- Naturality of the standard bases across a real-coordinate identification of two full-rank
period tori.

Declared as a `@[no_expose] def` rather than a `theorem` on purpose: the proof unfolds the
non-exposed `additiveTorusHomologyDegreeOne`, and the body of an exported theorem must be
checkable against the exposed interface alone. -/
@[no_expose] public def additiveTorusHomologyDegreeOne_naturality
    (x y : Parameters) (hx : FullRank x)
    (hy : FullRank y) (e : AdditiveTorus x ≃ₜ AdditiveTorus y)
    (he : ∀ z : ComplexTwoSpace,
      e (Quotient.mk _ z) = Quotient.mk _ (hy.realEquiv (hx.realEquiv.symm z)))
    (z : IntegralSingularHomology 1 (AdditiveTorus x)) :
    additiveTorusHomologyDegreeOne y hy
        (integralSingularHomologyMap 1 (e : C(AdditiveTorus x, AdditiveTorus y)) z) =
      additiveTorusHomologyDegreeOne x hx z := by
  rw [additiveTorusHomologyDegreeOne_apply, additiveTorusHomologyDegreeOne_apply]
  refine congrArg stdTorusFourHomologyOne ?_
  rw [integralSingularHomologyEquiv_eq_map, integralSingularHomologyMap_comp_wang,
    additiveTorusStdHomeomorph_comp_continuousMap x y hx hy e he,
    integralSingularHomologyEquiv_eq_map]

/-- The degree-two half of the same naturality statement.  See
`additiveTorusHomologyDegreeOne_naturality` for why this is a `@[no_expose] def`. -/
@[no_expose] public def additiveTorusHomologyDegreeTwo_naturality
    (x y : Parameters) (hx : FullRank x)
    (hy : FullRank y) (e : AdditiveTorus x ≃ₜ AdditiveTorus y)
    (he : ∀ z : ComplexTwoSpace,
      e (Quotient.mk _ z) = Quotient.mk _ (hy.realEquiv (hx.realEquiv.symm z)))
    (z : IntegralSingularHomology 2 (AdditiveTorus x)) :
    additiveTorusHomologyDegreeTwo y hy
        (integralSingularHomologyMap 2 (e : C(AdditiveTorus x, AdditiveTorus y)) z) =
      additiveTorusHomologyDegreeTwo x hx z := by
  rw [additiveTorusHomologyDegreeTwo_apply, additiveTorusHomologyDegreeTwo_apply]
  refine congrArg stdTorusFourHomologyTwo ?_
  rw [integralSingularHomologyEquiv_eq_map, integralSingularHomologyMap_comp_wang,
    additiveTorusStdHomeomorph_comp_continuousMap x y hx hy e he,
    integralSingularHomologyEquiv_eq_map]

end Bases

end StandardTorusHomologyGroups

end StandardTorusHomology

end SphereSixComplex

end

end
