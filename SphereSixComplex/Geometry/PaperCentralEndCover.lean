module

public import SphereSixComplex.Geometry.PuncturedAffineCompactCore
import all SphereSixComplex.TriangleGroup.Representation

/-!
# The three end cover of the paper's central family

The only established input used here is compactness of the explicit cofinite Fuchsian quotient
after removing a smaller selected horodisc.  All passage from base ends to the three concrete
collars is proved below.
-/

open CategoryTheory TopologicalSpace Topology

namespace SphereSixComplex.Geometry

open Set SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex Geometry
open ComplexTorus AnalyticTorusFamily TorusFamily GlobalTorusFamily
open EllipticWholeFiberCompactCover EllipticLinearCollarGlobalDescent
open EllipticPuncturedCollarGaugeHomeomorph EllipticVaryingFamilyQuotient
open EllipticCayleyHomeomorph
open EllipticLocalCoordinates
open EllipticHolomorphicLogCover
open CuspPeriodExpansion CuspPuncturedCollarBridge CuspCollarPairProperness
open EstablishedFuchsianCuspNeighborhood
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

noncomputable section

public theorem fuchsianSourceAction_isOpenMap (g : Delta) :
    IsOpenMap (fuchsianSourceAction g) := by
  apply (fuchsianSourceAction g).continuous_symm_iff.mp
  apply Continuous.congr (fuchsianSourceAction_contMDiff g⁻¹ 0).continuous
  intro z
  rw [map_inv]
  rfl

private theorem cyclicThree_cases (a : CyclicThree) :
    a = 1 ∨ a = Multiplicative.ofAdd (1 : ZMod 3) ∨
      a = Multiplicative.ofAdd (2 : ZMod 3) := by
  have hlt : a.toAdd.val < 3 := ZMod.val_lt a.toAdd
  interval_cases h : a.toAdd.val
  · left
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 3
    norm_num at h ⊢
    exact h
  · right; left
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 3
    norm_num at h ⊢
    exact h
  · right; right
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 3
    norm_num at h ⊢
    exact h

private theorem cyclicFour_cases (a : CyclicFour) :
    a = 1 ∨ a = Multiplicative.ofAdd (1 : ZMod 4) ∨
      a = Multiplicative.ofAdd (2 : ZMod 4) ∨
        a = Multiplicative.ofAdd (3 : ZMod 4) := by
  have hlt : a.toAdd.val < 4 := ZMod.val_lt a.toAdd
  interval_cases h : a.toAdd.val
  · left
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 4
    norm_num at h ⊢
    exact h
  · right; left
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 4
    norm_num at h ⊢
    exact h
  · right; right; left
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 4
    norm_num at h ⊢
    exact h
  · right; right; right
    apply Multiplicative.toAdd.injective
    apply ZMod.val_injective 4
    norm_num at h ⊢
    exact h

private theorem inl_two :
    Monoid.Coprod.inl (Multiplicative.ofAdd (2 : ZMod 3)) = g₁ * g₁ := by
  calc
    _ = Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 3) *
        Multiplicative.ofAdd (1 : ZMod 3)) := by congr 1
    _ = _ := by rw [map_mul]; rfl

private theorem inr_two :
    Monoid.Coprod.inr (Multiplicative.ofAdd (2 : ZMod 4)) = g₂ * g₂ := by
  calc
    _ = Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4) *
        Multiplicative.ofAdd (1 : ZMod 4)) := by congr 1
    _ = _ := by rw [map_mul]; rfl

private theorem inr_three :
    Monoid.Coprod.inr (Multiplicative.ofAdd (3 : ZMod 4)) = g₂ * g₂ * g₂ := by
  calc
    _ = Monoid.Coprod.inr ((Multiplicative.ofAdd (1 : ZMod 4) *
        Multiplicative.ofAdd (1 : ZMod 4)) *
          Multiplicative.ofAdd (1 : ZMod 4)) := by congr 1
    _ = _ := by rw [map_mul, map_mul]; rfl

public theorem orderThreeCayleyHomeomorph_norm_inl
    (a : CyclicThree) (z : UpperHalfPlane) :
    ‖(orderThreeCayleyHomeomorph
      (fuchsianSourceAction (Monoid.Coprod.inl a) • z) : ℂ)‖ =
      ‖(orderThreeCayleyHomeomorph z : ℂ)‖ := by
  rcases cyclicThree_cases a with rfl | rfl | rfl
  · rw [map_one]
    rfl
  · change ‖orderThreeCayley (fuchsianSourceAction g₁ • z)‖ =
      ‖orderThreeCayley z‖
    rw [orderThreeCayley_generator, norm_mul, norm_orderThreeMultiplier, one_mul]
  · rw [inl_two]
    change ‖orderThreeCayley (fuchsianSourceAction (g₁ * g₁) • z)‖ =
      ‖orderThreeCayley z‖
    rw [map_mul, mul_smul, orderThreeCayley_generator,
      orderThreeCayley_generator]
    rw [norm_mul, norm_mul, norm_orderThreeMultiplier]
    simp

public theorem orderFourCayleyHomeomorph_norm_inr
    (a : CyclicFour) (z : UpperHalfPlane) :
    ‖(orderFourCayleyHomeomorph
      (fuchsianSourceAction (Monoid.Coprod.inr a) • z) : ℂ)‖ =
      ‖(orderFourCayleyHomeomorph z : ℂ)‖ := by
  rcases cyclicFour_cases a with rfl | rfl | rfl | rfl
  · rw [map_one]
    rfl
  · change ‖orderFourCayley (fuchsianSourceAction g₂ • z)‖ =
      ‖orderFourCayley z‖
    rw [orderFourCayley_generator, norm_mul, norm_orderFourMultiplier, one_mul]
  · rw [inr_two]
    change ‖orderFourCayley (fuchsianSourceAction (g₂ * g₂) • z)‖ =
      ‖orderFourCayley z‖
    rw [map_mul, mul_smul, orderFourCayley_generator,
      orderFourCayley_generator]
    rw [norm_mul, norm_mul, norm_orderFourMultiplier]
    simp
  · rw [inr_three]
    change ‖orderFourCayley (fuchsianSourceAction (g₂ * g₂ * g₂) • z)‖ =
      ‖orderFourCayley z‖
    rw [map_mul, map_mul, mul_smul, mul_smul, orderFourCayley_generator,
      orderFourCayley_generator, orderFourCayley_generator]
    rw [norm_mul, norm_mul, norm_mul, norm_orderFourMultiplier]
    simp

namespace PaperAnalyticData

variable (P : PaperAnalyticData)

public theorem coordinate_image_cayleyBall_isOpen
    (cayley : UpperHalfPlane → ℂ) (hcayley : Continuous cayley)
    (b : ℝ) :
    IsOpen (P.modular.sourceCoordinate.coordinate ''
      {z : UpperHalfPlane | ‖cayley z‖ < b}) := by
  let B : Set UpperHalfPlane := {z | ‖cayley z‖ < b}
  let S : Set ℂ := P.modular.sourceCoordinate.coordinate '' B
  apply P.modular.sourceCoordinate.coordinate_isQuotientMap.isOpen_preimage.mp
  have hpreimage : P.modular.sourceCoordinate.coordinate ⁻¹' S =
      ⋃ g : Delta, (fun z : UpperHalfPlane ↦ fuchsianSourceAction g • z) '' B := by
    ext z
    constructor
    · rintro ⟨x, hxB, hxcoord⟩
      obtain ⟨g, hg⟩ :=
        (P.modular.sourceCoordinate.coordinate_eq_iff_orbit x z).mp hxcoord
      exact Set.mem_iUnion.mpr ⟨g, ⟨x, hxB, hg⟩⟩
    · intro hz
      obtain ⟨g, x, hxB, rfl⟩ := Set.mem_iUnion.mp hz
      refine ⟨x, hxB, ?_⟩
      exact P.modular.sourceCoordinate.coordinate_invariant g x |>.symm
  rw [hpreimage]
  apply isOpen_iUnion
  intro g
  apply fuchsianSourceAction_isOpenMap g
  exact (isOpen_lt
    (continuous_norm.comp hcayley) continuous_const)

public theorem exists_orderThree_coordinate_radius
    (b : ℝ) (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : UpperHalfPlane,
      ‖P.modular.sourceCoordinate.coordinate z‖ < δ →
        ∃ g : Delta,
          ‖(orderThreeCayleyHomeomorph (fuchsianSourceAction g • z) : ℂ)‖ < b := by
  let S := P.modular.sourceCoordinate.coordinate ''
    {z : UpperHalfPlane | ‖(orderThreeCayleyHomeomorph z : ℂ)‖ < b}
  have hSopen : IsOpen S := P.coordinate_image_cayleyBall_isOpen
    (fun z ↦ (orderThreeCayleyHomeomorph z : ℂ))
    (continuous_subtype_val.comp orderThreeCayleyHomeomorph.continuous) b
  have hzero : (0 : ℂ) ∈ S := by
    refine ⟨fuchsianOneFixedPoint, ?_,
      P.modular.sourceCoordinate.coordinate_at_one⟩
    simpa [orderThreeCayleyHomeomorph, cayleyHomeomorph,
      cayleyDiscCoordinate, orderThreeCayley_fixedPoint] using hb
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hSopen 0 hzero
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have hcoord : P.modular.sourceCoordinate.coordinate z ∈ S := by
    apply hball
    simpa [Metric.mem_ball, dist_zero_right] using hz
  obtain ⟨x, hx, hxcoord⟩ := hcoord
  obtain ⟨g, hg⟩ :=
    (P.modular.sourceCoordinate.coordinate_eq_iff_orbit x z).mp hxcoord
  refine ⟨g⁻¹, ?_⟩
  have hback : fuchsianSourceAction g⁻¹ • z = x := by
    rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  rw [hback]
  exact hx

public theorem exists_orderFour_coordinate_radius
    (b : ℝ) (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : UpperHalfPlane,
      ‖P.modular.sourceCoordinate.coordinate z - 1‖ < δ →
        ∃ g : Delta,
          ‖(orderFourCayleyHomeomorph (fuchsianSourceAction g • z) : ℂ)‖ < b := by
  let S := P.modular.sourceCoordinate.coordinate ''
    {z : UpperHalfPlane | ‖(orderFourCayleyHomeomorph z : ℂ)‖ < b}
  have hSopen : IsOpen S := P.coordinate_image_cayleyBall_isOpen
    (fun z ↦ (orderFourCayleyHomeomorph z : ℂ))
    (continuous_subtype_val.comp orderFourCayleyHomeomorph.continuous) b
  have hone : (1 : ℂ) ∈ S := by
    refine ⟨fuchsianTwoFixedPoint, ?_,
      P.modular.sourceCoordinate.coordinate_at_two⟩
    simpa [orderFourCayleyHomeomorph, cayleyHomeomorph,
      cayleyDiscCoordinate, orderFourCayley_fixedPoint] using hb
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hSopen 1 hone
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have hcoord : P.modular.sourceCoordinate.coordinate z ∈ S := by
    apply hball
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  obtain ⟨x, hx, hxcoord⟩ := hcoord
  obtain ⟨g, hg⟩ :=
    (P.modular.sourceCoordinate.coordinate_eq_iff_orbit x z).mp hxcoord
  refine ⟨g⁻¹, ?_⟩
  have hback : fuchsianSourceAction g⁻¹ • z = x := by
    rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  rw [hback]
  exact hx

/-- A path contained in a sufficiently small order-three affine neighborhood has finite-order
deck monodromy.  The proof moves its initial point into the linear collar and uses connectedness
to keep the whole translated path there. -/
public theorem orderThree_path_deck_isOfFinOrder_of_coordinate_small
    {R inner delta : ℝ} (hinnerR : inner < R)
    (D : OrderThreeLinearCollarSourceData
      (U := P.modular.modularParameter.toTriangleUniformization) R)
    (hcoordinate : ∀ z : UpperHalfPlane,
      ‖P.modular.sourceCoordinate.coordinate z‖ < delta →
        ∃ k : Delta,
          ‖(orderThreeCayleyHomeomorph
            (fuchsianSourceAction k • z) : ℂ)‖ < inner)
    (z : UpperHalfPlane) (g : Delta)
    (Q : Path z (fuchsianSourceAction g • z))
    (hQ : ∀ t, ‖P.modular.sourceCoordinate.coordinate (Q t)‖ < delta) :
    IsOfFinOrder g := by
  let middle := (inner + R) / 2
  have hinnerMiddle : inner < middle := by dsimp [middle]; linarith
  have hmiddleR : middle < R := by dsimp [middle]; linarith
  obtain ⟨h, hh⟩ := hcoordinate z (by simpa using hQ 0)
  have hstay : ∀ t, ‖(orderThreeCayleyHomeomorph
      (fuchsianSourceAction h • Q t) : ℂ)‖ < middle := by
    intro t
    by_contra hnot
    have hge : middle ≤ ‖(orderThreeCayleyHomeomorph
        (fuchsianSourceAction h • Q t) : ℂ)‖ := le_of_not_gt hnot
    let f : unitInterval → ℝ := fun u ↦
      ‖(orderThreeCayleyHomeomorph
        (fuchsianSourceAction h • Q u) : ℂ)‖
    have hf : Continuous f := by
      apply continuous_norm.comp
      exact (continuous_subtype_val.comp orderThreeCayleyHomeomorph.continuous).comp
        ((fuchsianSourceAction_contMDiff h 0).continuous.comp Q.continuous)
    have hfzero : f 0 < middle := by simpa [f] using hh.trans hinnerMiddle
    have hmem : middle ∈ Set.Icc (f 0) (f t) := ⟨hfzero.le, hge⟩
    obtain ⟨u, hu⟩ := (intermediate_value_univ 0 t hf) hmem
    obtain ⟨k, hk⟩ := hcoordinate (Q u) (hQ u)
    rw [OrderThreeLinearCollarSourceData.eq_def] at D
    obtain ⟨a, ha⟩ := D.2
      (fuchsianSourceAction h • Q u)
      (fuchsianSourceAction k • Q u)
      (by
        change f u < R
        rw [hu]
        exact hmiddleR)
      (hk.trans hinnerR) (h * k⁻¹) (by
        rw [P.modular.modularParameter.toTriangleUniformization_sourceAction]
        rw [map_mul, map_inv, mul_smul, inv_smul_smul])
    have heq : ‖(orderThreeCayleyHomeomorph
        (fuchsianSourceAction h • Q u) : ℂ)‖ =
        ‖(orderThreeCayleyHomeomorph
          (fuchsianSourceAction k • Q u) : ℂ)‖ := by
      rw [← show fuchsianSourceAction (h * k⁻¹) •
            (fuchsianSourceAction k • Q u) =
          fuchsianSourceAction h • Q u by
            rw [map_mul, map_inv, mul_smul, inv_smul_smul], ha]
      exact orderThreeCayleyHomeomorph_norm_inl a _
    have : middle < inner := by
      calc
        middle = ‖(orderThreeCayleyHomeomorph
            (fuchsianSourceAction h • Q u) : ℂ)‖ := hu.symm
        _ = ‖(orderThreeCayleyHomeomorph
            (fuchsianSourceAction k • Q u) : ℂ)‖ := heq
        _ < inner := hk
    exact (not_lt_of_ge hinnerMiddle.le) this
  rw [OrderThreeLinearCollarSourceData.eq_def] at D
  obtain ⟨a, ha⟩ := D.2
    (fuchsianSourceAction h • (fuchsianSourceAction g • z))
    (fuchsianSourceAction h • z)
    (by simpa [Q.target] using (hstay 1).trans hmiddleR)
    (hh.trans hinnerR) (h * g * h⁻¹) (by
      rw [P.modular.modularParameter.toTriangleUniformization_sourceAction]
      simp only [map_mul, map_inv, mul_smul, inv_smul_smul])
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨3, by norm_num, ?_⟩
  have ha3 : (Monoid.Coprod.inl a : Delta) ^ 3 = 1 := by
    have haPow : a ^ 3 = 1 := by
      rcases cyclicThree_cases a with rfl | rfl | rfl
      · simp
      · decide
      · decide
    rw [← map_pow, haPow, map_one]
  have hpow := congrArg (fun x : Delta ↦ x ^ 3) ha
  rw [conj_pow, ha3] at hpow
  calc
    g ^ 3 = h⁻¹ * (h * g ^ 3 * h⁻¹) * h := by group
    _ = 1 := by rw [hpow]; group

/-- A path contained in a sufficiently small order-four affine neighborhood has finite-order
deck monodromy. -/
public theorem orderFour_path_deck_isOfFinOrder_of_coordinate_small
    {R inner delta : ℝ} (hinnerR : inner < R)
    (D : OrderFourLinearCollarSourceData
      (U := P.modular.modularParameter.toTriangleUniformization) R)
    (hcoordinate : ∀ z : UpperHalfPlane,
      ‖P.modular.sourceCoordinate.coordinate z - 1‖ < delta →
        ∃ k : Delta,
          ‖(orderFourCayleyHomeomorph
            (fuchsianSourceAction k • z) : ℂ)‖ < inner)
    (z : UpperHalfPlane) (g : Delta)
    (Q : Path z (fuchsianSourceAction g • z))
    (hQ : ∀ t, ‖P.modular.sourceCoordinate.coordinate (Q t) - 1‖ < delta) :
    IsOfFinOrder g := by
  let middle := (inner + R) / 2
  have hinnerMiddle : inner < middle := by dsimp [middle]; linarith
  have hmiddleR : middle < R := by dsimp [middle]; linarith
  obtain ⟨h, hh⟩ := hcoordinate z (by simpa using hQ 0)
  have hstay : ∀ t, ‖(orderFourCayleyHomeomorph
      (fuchsianSourceAction h • Q t) : ℂ)‖ < middle := by
    intro t
    by_contra hnot
    have hge : middle ≤ ‖(orderFourCayleyHomeomorph
        (fuchsianSourceAction h • Q t) : ℂ)‖ := le_of_not_gt hnot
    let f : unitInterval → ℝ := fun u ↦
      ‖(orderFourCayleyHomeomorph
        (fuchsianSourceAction h • Q u) : ℂ)‖
    have hf : Continuous f := by
      apply continuous_norm.comp
      exact (continuous_subtype_val.comp orderFourCayleyHomeomorph.continuous).comp
        ((fuchsianSourceAction_contMDiff h 0).continuous.comp Q.continuous)
    have hfzero : f 0 < middle := by simpa [f] using hh.trans hinnerMiddle
    have hmem : middle ∈ Set.Icc (f 0) (f t) := ⟨hfzero.le, hge⟩
    obtain ⟨u, hu⟩ := (intermediate_value_univ 0 t hf) hmem
    obtain ⟨k, hk⟩ := hcoordinate (Q u) (hQ u)
    rw [OrderFourLinearCollarSourceData.eq_def] at D
    obtain ⟨a, ha⟩ := D.2
      (fuchsianSourceAction h • Q u)
      (fuchsianSourceAction k • Q u)
      (by
        change f u < R
        rw [hu]
        exact hmiddleR)
      (hk.trans hinnerR) (h * k⁻¹) (by
        rw [P.modular.modularParameter.toTriangleUniformization_sourceAction]
        rw [map_mul, map_inv, mul_smul, inv_smul_smul])
    have heq : ‖(orderFourCayleyHomeomorph
        (fuchsianSourceAction h • Q u) : ℂ)‖ =
        ‖(orderFourCayleyHomeomorph
          (fuchsianSourceAction k • Q u) : ℂ)‖ := by
      rw [← show fuchsianSourceAction (h * k⁻¹) •
            (fuchsianSourceAction k • Q u) =
          fuchsianSourceAction h • Q u by
            rw [map_mul, map_inv, mul_smul, inv_smul_smul], ha]
      exact orderFourCayleyHomeomorph_norm_inr a _
    have : middle < inner := by
      calc
        middle = ‖(orderFourCayleyHomeomorph
            (fuchsianSourceAction h • Q u) : ℂ)‖ := hu.symm
        _ = ‖(orderFourCayleyHomeomorph
            (fuchsianSourceAction k • Q u) : ℂ)‖ := heq
        _ < inner := hk
    exact (not_lt_of_ge hinnerMiddle.le) this
  rw [OrderFourLinearCollarSourceData.eq_def] at D
  obtain ⟨a, ha⟩ := D.2
    (fuchsianSourceAction h • (fuchsianSourceAction g • z))
    (fuchsianSourceAction h • z)
    (by simpa [Q.target] using (hstay 1).trans hmiddleR)
    (hh.trans hinnerR) (h * g * h⁻¹) (by
      rw [P.modular.modularParameter.toTriangleUniformization_sourceAction]
      simp only [map_mul, map_inv, mul_smul, inv_smul_smul])
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨4, by norm_num, ?_⟩
  have ha4 : (Monoid.Coprod.inr a : Delta) ^ 4 = 1 := by
    have haPow : a ^ 4 = 1 := by
      rcases cyclicFour_cases a with rfl | rfl | rfl | rfl
      · simp
      · decide
      · decide
      · decide
    rw [← map_pow, haPow, map_one]
  have hpow := congrArg (fun x : Delta ↦ x ^ 4) ha
  rw [conj_pow, ha4] at hpow
  calc
    g ^ 4 = h⁻¹ * (h * g ^ 4 * h⁻¹) * h := by group
    _ = 1 := by rw [hpow]; group

public theorem centralQuotientProjection_familyDeckMap
    (g : Delta) (q : RegularTotalSpace P.periods) :
    P.centralQuotientProjection (regularFamilyDeckMap P.periods g q) =
      P.centralQuotientProjection q := by
  let _ := regularFamilyDeckAction P.periods
  rw [centralQuotientProjection.eq_def, quotientProjection.eq_def]
  apply Quotient.sound
  change MulAction.orbitRel Delta (RegularTotalSpace P.periods)
    (regularFamilyDeckMap P.periods g q) q
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨g, rfl⟩

public theorem exists_orderThree_starCollar_of_baseRadius
    (q : RegularTotalSpace P.periods) (g : Delta) (b : ℝ)
    (hb : ‖(orderThreeCayleyHomeomorph
      (fuchsianSourceAction g • (regularTotalSpaceBase P.periods q).1) : ℂ)‖ < b)
    (hbouter : b < P.starSeparation.orderThree.radius) :
    ∃ z : P.starCollarSourceType (1 : Fin 3),
      P.starToCentral (1 : Fin 3) z = P.centralQuotientProjection q ∧
        P.starCollarRadius (1 : Fin 3) z < b := by
  let qg := regularFamilyDeckMap P.periods g q
  have hbase : (regularTotalSpaceBase P.periods qg).1 =
      fuchsianSourceAction g • (regularTotalSpaceBase P.periods q).1 := by
    dsimp only [qg]
    rw [regularTotalSpaceBase_familyDeckMap]
    rfl
  have hpositive : 0 < orderThreeFamilyRadius P.periods
      (regularFamilyInclusion P.periods qg) := by
    rw [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_regularFamilyInclusion, hbase]
    apply norm_pos_iff.mpr
    apply coe_ne_zero_of_ne_center
    intro heq
    have hfixed : fuchsianSourceAction g •
        (regularTotalSpaceBase P.periods q).1 = fuchsianOneFixedPoint := by
      apply orderThreeCayleyHomeomorph.injective
      simpa [orderThreeCayleyHomeomorph, cayleyHomeomorph, cayleyDiscCoordinate,
        discCenter, orderThreeCayley_fixedPoint] using heq
    have hregular := isRegularBasePoint_smul
      (U := P.modular.modularParameter.toTriangleUniformization) g
      (regularTotalSpaceBase P.periods q).property
    have hmem := (P.isRegularBasePoint_iff_coordinate_mem _).mp hregular
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
    exact hmem.1 (hfixed ▸ P.modular.sourceCoordinate.coordinate_at_one)
  let qlin : orderThreePuncturedFamilyCollar P.periods
      P.starSeparation.orderThree.radius :=
    ⟨regularFamilyInclusion P.periods qg, by
      rw [orderThreePuncturedFamilyCollar.eq_def]
      refine ⟨hpositive, ?_⟩
      rw [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_regularFamilyInclusion, hbase]
      exact hb.trans hbouter⟩
  let x := (orderThreePuncturedCollarGaugeEquiv P.periods
    P.starSeparation.orderThree.radius).symm qlin
  let z : P.starCollarSourceType (1 : Fin 3) := Quotient.mk _ x
  refine ⟨z, ?_, ?_⟩
  · rw [P.orderThreeStarToCentral_mk x]
    have hregularEq : orderThreeCollarToRegular P.periods
        (sourceActionProperlyDiscontinuous_of_eq
          P.modular.modularParameter.toTriangleUniformization_sourceAction)
        P.starSeparation.orderThree.sourceData
        (orderThreePuncturedCollarGaugeEquiv P.periods
          P.starSeparation.orderThree.radius x) = qg := by
      apply regularFamilyInclusion_injective P.periods
      simpa [x, qlin] using regularFamilyInclusion_orderThreeCollarToRegular P.periods
        (sourceActionProperlyDiscontinuous_of_eq
          P.modular.modularParameter.toTriangleUniformization_sourceAction)
        P.starSeparation.orderThree.sourceData qlin
    rw [hregularEq]
    exact P.centralQuotientProjection_familyDeckMap g q
  · rw [P.orderThreeStarCollarRadius_mk x]
    change orderThreeFamilyRadius P.periods
      ((orderThreePrincipalGaugeEquiv P.periods).symm qlin.1) < b
    rw [orderThreeFamilyRadius_principalGauge_symm]
    change orderThreeFamilyRadius P.periods
      (regularFamilyInclusion P.periods qg) < b
    rw [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_regularFamilyInclusion, hbase]
    exact hb

public theorem exists_orderFour_starCollar_of_baseRadius
    (q : RegularTotalSpace P.periods) (g : Delta) (b : ℝ)
    (hb : ‖(orderFourCayleyHomeomorph
      (fuchsianSourceAction g • (regularTotalSpaceBase P.periods q).1) : ℂ)‖ < b)
    (hbouter : b < P.starSeparation.orderFour.radius) :
    ∃ z : P.starCollarSourceType (2 : Fin 3),
      P.starToCentral (2 : Fin 3) z = P.centralQuotientProjection q ∧
        P.starCollarRadius (2 : Fin 3) z < b := by
  let qg := regularFamilyDeckMap P.periods g q
  have hbase : (regularTotalSpaceBase P.periods qg).1 =
      fuchsianSourceAction g • (regularTotalSpaceBase P.periods q).1 := by
    dsimp only [qg]
    rw [regularTotalSpaceBase_familyDeckMap]
    rfl
  have hpositive : 0 < orderFourFamilyRadius P.periods
      (regularFamilyInclusion P.periods qg) := by
    rw [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_regularFamilyInclusion, hbase]
    apply norm_pos_iff.mpr
    apply coe_ne_zero_of_ne_center
    intro heq
    have hfixed : fuchsianSourceAction g •
        (regularTotalSpaceBase P.periods q).1 = fuchsianTwoFixedPoint := by
      apply orderFourCayleyHomeomorph.injective
      simpa [orderFourCayleyHomeomorph, cayleyHomeomorph, cayleyDiscCoordinate,
        discCenter, orderFourCayley_fixedPoint] using heq
    have hregular := isRegularBasePoint_smul
      (U := P.modular.modularParameter.toTriangleUniformization) g
      (regularTotalSpaceBase P.periods q).property
    have hmem := (P.isRegularBasePoint_iff_coordinate_mem _).mp hregular
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
    exact hmem.2 (hfixed ▸ P.modular.sourceCoordinate.coordinate_at_two)
  let qlin : orderFourPuncturedFamilyCollar P.periods
      P.starSeparation.orderFour.radius :=
    ⟨regularFamilyInclusion P.periods qg, by
      rw [orderFourPuncturedFamilyCollar.eq_def]
      refine ⟨hpositive, ?_⟩
      rw [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_regularFamilyInclusion, hbase]
      exact hb.trans hbouter⟩
  let x := (orderFourPuncturedCollarGaugeEquiv P.periods
    P.starSeparation.orderFour.radius).symm qlin
  let z : P.starCollarSourceType (2 : Fin 3) := Quotient.mk _ x
  refine ⟨z, ?_, ?_⟩
  · rw [P.orderFourStarToCentral_mk x]
    have hregularEq : orderFourCollarToRegular P.periods
        (sourceActionProperlyDiscontinuous_of_eq
          P.modular.modularParameter.toTriangleUniformization_sourceAction)
        P.starSeparation.orderFour.sourceData
        (orderFourPuncturedCollarGaugeEquiv P.periods
          P.starSeparation.orderFour.radius x) = qg := by
      apply regularFamilyInclusion_injective P.periods
      simpa [x, qlin] using regularFamilyInclusion_orderFourCollarToRegular P.periods
        (sourceActionProperlyDiscontinuous_of_eq
          P.modular.modularParameter.toTriangleUniformization_sourceAction)
        P.starSeparation.orderFour.sourceData qlin
    rw [hregularEq]
    exact P.centralQuotientProjection_familyDeckMap g q
  · rw [P.orderFourStarCollarRadius_mk x]
    change orderFourFamilyRadius P.periods
      ((orderFourPrincipalGaugeEquiv P.periods).symm qlin.1) < b
    rw [orderFourFamilyRadius_principalGauge_symm]
    change orderFourFamilyRadius P.periods
      (regularFamilyInclusion P.periods qg) < b
    rw [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_regularFamilyInclusion, hbase]
    exact hb

public theorem exists_cusp_starCollar_of_normalizedBase
    (q : RegularTotalSpace P.periods) (g : Delta) (s : ℂ)
    (hs : s ∈ cuspHalfPlane P.cuspCoordinate.height)
    (hbase : fuchsianSourceAction g • (regularTotalSpaceBase P.periods q).1 =
      P.cuspCoordinate.lift s)
    (b : ℝ) (hb : ‖cuspQ s‖ < b)
    (hbouter : b < P.starCuspWitness.localWitness.radius) :
    ∃ z : P.starCollarSourceType (0 : Fin 3),
      P.starToCentral (0 : Fin 3) z = P.centralQuotientProjection q ∧
        P.starCollarRadius (0 : Fin 3) z < b := by
  let W := P.starCuspWitness
  let qg := regularFamilyDeckMap P.periods g q
  have hqgbase : regularTotalSpaceBase P.periods qg =
      (⟨P.cuspCoordinate.lift s,
        W.lift_regular hs (hb.trans hbouter)⟩ :
          RegularBase
            (U := P.modular.modularParameter.toTriangleUniformization)) := by
    apply Subtype.ext
    dsimp only [qg]
    rw [regularTotalSpaceBase_familyDeckMap]
    exact hbase
  obtain ⟨r, hr, hrq⟩ := P.exists_regularFamilyBaseCubeParam_eq qg
  let v := (fullRankDomain
    (regularParameterMap P.periods (regularTotalSpaceBase P.periods qg))).realEquiv r
  let target : {x : RegularBase
      (U := P.modular.modularParameter.toTriangleUniformization) × ComplexTwoSpace |
      x.1.1 ∈ normalizedCuspRegion P.cuspCoordinate W.localWitness.radius} :=
    ⟨(regularTotalSpaceBase P.periods qg, v), by
      rw [hqgbase]
      exact ⟨s, ⟨hs, hb.trans hbouter⟩, rfl⟩⟩
  let p : additiveCuspRadiusCover W.localWitness.radius :=
    (additiveCuspBundleHomeomorph W).symm target
  have hpimage : additiveCuspBundleHomeomorph W p = target :=
    (additiveCuspBundleHomeomorph W).apply_symm_apply target
  have hplift : P.cuspCoordinate.lift p.1.2 = P.cuspCoordinate.lift s := by
    have h := congrArg (fun x : {x : RegularBase
        (U := P.modular.modularParameter.toTriangleUniformization) × ComplexTwoSpace |
        x.1.1 ∈ normalizedCuspRegion P.cuspCoordinate W.localWitness.radius} ↦ x.1.1.1)
      hpimage
    simpa [additiveCuspBundleHomeomorph, target, hqgbase] using h
  have hpHalf : p.1.2 ∈ cuspHalfPlane P.cuspCoordinate.height :=
    additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p
  have hps : p.1.2 = s := by
    have h := congrArg (fun z : UpperHalfPlane ↦
      (((assembledFuchsianPeriodFunctions P.modular P.localPeriods).tau z :
        UpperHalfPlane) : ℂ)) hplift
    rw [P.cuspCoordinate.lift_tau p.1.2 hpHalf,
      P.cuspCoordinate.lift_tau s hs] at h
    exact h
  let z : P.starCollarSourceType (0 : Fin 3) :=
    additiveCuspCoverToPuncturedQuotient W p
  refine ⟨z, ?_, ?_⟩
  · change puncturedLocalCuspQuotientMap W
      (additiveCuspCoverToPuncturedQuotient W p) =
        P.centralQuotientProjection q
    rw [puncturedLocalCuspQuotientMap_additiveCover]
    rw [additiveCuspCoverToGlobal_eq_quotientProjections]
    rw [hpimage]
    change P.centralQuotientProjection
      (P.regularFamilyBaseCubeParam
        (regularTotalSpaceBase P.periods qg, r)) = _
    rw [hrq]
    exact P.centralQuotientProjection_familyDeckMap g q
  · change puncturedLocalCuspRadius W
      (additiveCuspCoverToPuncturedQuotient W p) < b
    rw [puncturedLocalCuspRadius_additiveCover, hps]
    exact hb

public theorem starOuterRadius_pos (i : Fin 3) :
    0 < P.starOuterRadius i := by
  fin_cases i
  · exact P.starCuspWitness.localWitness.radius_pos
  · exact P.starSeparation.orderThree.radius_pos
  · exact P.starSeparation.orderFour.radius_pos

/-- The compact affine-coordinate core obtained by truncating all three central ends. -/
@[expose] public noncomputable def thresholdedCentralEndCoverData :
    P.ThresholdedCentralEndCoverData := by
  let a : Fin 3 → ℝ := fun i ↦ P.starOuterRadius i / 2
  have ha_pos (i : Fin 3) : 0 < a i := half_pos (starOuterRadius_pos P i)
  have ha_outer (i : Fin 3) : a i < P.starOuterRadius i :=
    half_lt_self (starOuterRadius_pos P i)
  let cuspUpper := P.starCuspWitness.localWitness.radius / 4
  have hcuspUpper : 0 < cuspUpper := by
    exact div_pos P.starCuspWitness.localWitness.radius_pos (by norm_num)
  let H : EstablishedFuchsianCuspNeighborhood.Data P.cuspCoordinate cuspUpper :=
    Classical.choice
      (EstablishedFuchsianCuspNeighborhood.Established.data
        P.cuspCoordinate cuspUpper hcuspUpper)
  let T : EstablishedFuchsianCuspNeighborhood.CompactTruncationData H :=
    Classical.choice
      (EstablishedFuchsianCuspNeighborhood.Established.compactTruncation H)
  have hH_threshold : H.radius < a 0 := by
    have hle := H.radius_le_upper
    change H.radius ≤ P.starCuspWitness.localWitness.radius / 4 at hle
    change H.radius < P.starCuspWitness.localWitness.radius / 2
    linarith [P.starCuspWitness.localWitness.radius_pos]
  have hH_outer : H.radius < P.starCuspWitness.localWitness.radius := by
    exact hH_threshold.trans (ha_outer 0)
  let threeExistence := exists_orderThree_coordinate_radius P (a 1) (ha_pos 1)
  let deltaThree := Classical.choose threeExistence
  have hdeltaThree : 0 < deltaThree := (Classical.choose_spec threeExistence).1
  have hthree := (Classical.choose_spec threeExistence).2
  let fourExistence := exists_orderFour_coordinate_radius P (a 2) (ha_pos 2)
  let deltaFour := Classical.choose fourExistence
  have hdeltaFour : 0 < deltaFour := (Classical.choose_spec fourExistence).1
  have hfour := (Classical.choose_spec fourExistence).2
  have hcoordinateCompact : IsCompact
      (P.modular.sourceCoordinate.coordinate '' T.core) :=
    T.core_isCompact.image P.modular.sourceCoordinate.coordinate_holomorphic.continuous
  let boundExistence := hcoordinateCompact.isBounded.exists_norm_le
  let R := Classical.choose boundExistence
  have hR := Classical.choose_spec boundExistence
  let K := puncturedAffineThresholdCore deltaThree deltaFour R
  have hKcompact : IsCompact K :=
    puncturedAffineThresholdCore_isCompact hdeltaThree hdeltaFour
  have hcentralCover : ∀ q : RegularTotalSpace P.periods,
      P.regularCoordinate (regularTotalSpaceBase P.periods q) ∉ K →
        ∃ (i : Fin 3) (z : P.starCollarSourceType i),
          P.starToCentral i z = P.centralQuotientProjection q ∧
            P.starCollarRadius i z ≤ a i := by
    intro q hq
    have hends := not_mem_puncturedAffineThresholdCore hq
    rcases hends with hthreeEnd | hfourEnd | hcuspEnd
    · obtain ⟨g, hg⟩ := hthree (regularTotalSpaceBase P.periods q).1 hthreeEnd
      obtain ⟨z, hzCentral, hzRadius⟩ :=
        exists_orderThree_starCollar_of_baseRadius P q g (a 1) hg (ha_outer 1)
      exact ⟨1, z, hzCentral, hzRadius.le⟩
    · obtain ⟨g, hg⟩ := hfour (regularTotalSpaceBase P.periods q).1 hfourEnd
      obtain ⟨z, hzCentral, hzRadius⟩ :=
        exists_orderFour_starCollar_of_baseRadius P q g (a 2) hg (ha_outer 2)
      exact ⟨2, z, hzCentral, hzRadius.le⟩
    · obtain ⟨g, hgCusp | hgCore⟩ :=
        T.orbit_covers (regularTotalSpaceBase P.periods q).1
      · obtain ⟨s, ⟨hs, hsq⟩, hbase⟩ := hgCusp
        obtain ⟨z, hzCentral, hzRadius⟩ :=
          exists_cusp_starCollar_of_normalizedBase P q g s hs hbase.symm
            H.radius hsq hH_outer
        exact ⟨0, z, hzCentral, hzRadius.le.trans hH_threshold.le⟩
      · have hbound : ‖P.modular.sourceCoordinate.coordinate
            (fuchsianSourceAction g • (regularTotalSpaceBase P.periods q).1)‖ ≤ R :=
          hR _ ⟨_, hgCore, rfl⟩
        rw [P.modular.sourceCoordinate.coordinate_invariant] at hbound
        exact (not_lt_of_ge hbound hcuspEnd).elim
  refine
    { coordinateSubset := K
      coordinateSubset_isCompact := hKcompact
      threshold := a
      threshold_nonneg := fun i ↦ (ha_pos i).le
      threshold_lt_outer := ha_outer
      centralEnd_covers := hcentralCover
      outerCentral_coordinate := ?_ }
  intro i z q hq hz
  by_contra hnot
  obtain ⟨j, w, hw, hwRadius⟩ := hcentralCover q hnot
  have heq : P.starToCentral j w = P.starToCentral i z := hw.trans hq
  by_cases hji : j = i
  · subst j
    have hwz := (P.starToCentral_isOpenEmbedding i).injective heq
    subst w
    exact (not_lt_of_ge hwRadius) hz
  · have hdisjoint := P.starToCentral_ranges_pairwise hji
    exact (Set.disjoint_left.mp hdisjoint ⟨w, rfl⟩ ⟨z, heq.symm⟩).elim

/-- The paper's central quotient is covered outside a compact coordinate core by the three
selected cusp and elliptic collars, with a strict inner threshold in each collar. -/
public theorem thresholdedCentralEndCoverExistence :
    P.ThresholdedCentralEndCoverExistence :=
  ⟨P.thresholdedCentralEndCoverData⟩

end PaperAnalyticData

end

end SphereSixComplex.Geometry
