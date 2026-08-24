module

public import SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
import all SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
import all SphereSixComplex.TriangleGroup.FuchsianAction
import all SphereSixComplex.TriangleGroup.FreeProductTorsion

/-!
# Ping-pong regions for the explicit Fuchsian action

The imaginary axis separates two ping-pong regions.  Every nonidentity element of the
order-three factor moves the left region into the right region, while every nonidentity element
of the order-four factor moves the right region into the left region.
-/

noncomputable section

namespace SphereSixComplex.TriangleGroup.FuchsianPingPong

open Cardinal
open SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
open scoped Function
open scoped Pointwise

/-- The open half-plane to the right of the imaginary axis. -/
@[expose] public def rightRegion : Set UpperHalfPlane := {z | 0 < z.re}

/-- The open half-plane to the left of the imaginary axis. -/
@[expose] public def leftRegion : Set UpperHalfPlane := {z | z.re < 0}

public theorem gOne_maps_left_to_right :
    fuchsianSourceAction g₁ • leftRegion ⊆ rightRegion := by
  rintro _ ⟨z, hz, rfl⟩
  change z.re < 0 at hz
  change 0 < (fuchsianSourceAction g₁ • z).re
  have hre := congrArg Complex.re (fuchsianSourceAction_g₁_apply z)
  rw [Complex.div_re] at hre
  norm_num at hre
  have hnorm : 0 < Complex.normSq (z : ℂ) := z.normSq_pos
  rw [fuchsianSourceAction_g₁]
  change 0 < (fuchsianOnePerm z).re
  rw [hre]
  rw [← add_div]
  apply div_pos
  · nlinarith [sq_pos_of_pos z.im_pos]
  · exact hnorm

public theorem gOne_sq_apply (z : UpperHalfPlane) :
    (((fuchsianSourceAction (g₁ ^ 2)) z : UpperHalfPlane) : ℂ) = 1 / (1 - z) := by
  calc
    (((fuchsianSourceAction (g₁ ^ 2)) z : UpperHalfPlane) : ℂ) =
        (((fuchsianSourceAction g₁)
          (fuchsianSourceAction g₁ z) : UpperHalfPlane) : ℂ) := by
      rw [map_pow, pow_two]
      rfl
    _ = ((fuchsianSourceAction g₁ z : UpperHalfPlane) - 1) /
        (fuchsianSourceAction g₁ z : UpperHalfPlane) :=
      fuchsianSourceAction_g₁_apply (fuchsianSourceAction g₁ z)
    _ = 1 / (1 - z) := by
      rw [fuchsianSourceAction_g₁_apply]
      have hzsub : (z : ℂ) - 1 ≠ 0 := by
        intro hzero
        have him := congrArg Complex.im hzero
        norm_num at him
        exact z.im_pos.ne' him
      have honeSub : 1 - (z : ℂ) ≠ 0 := by
        intro hzero
        have him := congrArg Complex.im hzero
        norm_num at him
        exact z.im_pos.ne' him
      field_simp [z.ne_zero, hzsub, honeSub]
      ring

public theorem gOne_sq_maps_left_to_right :
    fuchsianSourceAction (g₁ ^ 2) • leftRegion ⊆ rightRegion := by
  rintro _ ⟨z, hz, rfl⟩
  change z.re < 0 at hz
  change 0 < (fuchsianSourceAction (g₁ ^ 2) • z).re
  have hre := congrArg Complex.re (gOne_sq_apply z)
  rw [Complex.div_re] at hre
  norm_num at hre
  have hnorm : 0 < Complex.normSq (1 - (z : ℂ)) := by
    rw [Complex.normSq_pos]
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    exact z.im_pos.ne' him
  rw [map_pow]
  change 0 < ((fuchsianOnePerm ^ 2) z).re
  rw [hre]
  exact div_pos (by linarith) hnorm

public theorem gTwo_maps_right_to_left :
    fuchsianSourceAction g₂ • rightRegion ⊆ leftRegion := by
  rintro _ ⟨z, hz, rfl⟩
  change 0 < z.re at hz
  change (fuchsianSourceAction g₂ • z).re < 0
  have hre := congrArg Complex.re (fuchsianSourceAction_g₂_apply z)
  rw [Complex.div_re] at hre
  norm_num at hre
  have hnorm : 0 < Complex.normSq ((z : ℂ) + Real.sqrt 2) := by
    rw [Complex.normSq_pos]
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    exact z.im_pos.ne' him
  rw [fuchsianSourceAction_g₂]
  change (fuchsianTwoPerm z).re < 0
  rw [hre]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact div_neg_of_neg_of_pos (by linarith) hnorm

public theorem gTwo_sq_maps_right_to_left :
    fuchsianSourceAction (g₂ ^ 2) • rightRegion ⊆ leftRegion := by
  rintro _ ⟨z, hz, rfl⟩
  change 0 < z.re at hz
  change (fuchsianSourceAction (g₂ ^ 2) • z).re < 0
  have hre := congrArg Complex.re
    (FreeProductTorsion.fuchsianSourceAction_gTwo_sq_apply z)
  rw [Complex.div_re] at hre
  norm_num at hre
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hnorm : 0 < Complex.normSq (Real.sqrt 2 * (z : ℂ) + 1) := by
    rw [Complex.normSq_pos]
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    nlinarith [z.im_pos]
  rw [map_pow]
  change ((fuchsianTwoPerm ^ 2) z).re < 0
  rw [hre]
  rw [← add_div]
  apply div_neg_of_neg_of_pos
  · have hneg : -z.re - Real.sqrt 2 < 0 := by linarith
    have hpos : 0 < Real.sqrt 2 * z.re + 1 := by nlinarith [mul_pos hsqrt hz]
    have hreal := mul_neg_of_neg_of_pos hneg hpos
    have himag : 0 < z.im * (Real.sqrt 2 * z.im) := by positivity
    linarith
  · exact hnorm

public theorem gTwo_cube_apply (z : UpperHalfPlane) :
    (((fuchsianSourceAction (g₂ ^ 3)) z : UpperHalfPlane) : ℂ) =
      -Real.sqrt 2 - 1 / z := by
  calc
    (((fuchsianSourceAction (g₂ ^ 3)) z : UpperHalfPlane) : ℂ) =
        (((fuchsianSourceAction (g₂ ^ 2))
          (fuchsianSourceAction g₂ z) : UpperHalfPlane) : ℂ) := by
      rw [show g₂ ^ 3 = g₂ ^ 2 * g₂ by group, map_mul]
      rfl
    _ = (-(fuchsianSourceAction g₂ z : UpperHalfPlane) - Real.sqrt 2) /
        (Real.sqrt 2 * (fuchsianSourceAction g₂ z : UpperHalfPlane) + 1) :=
      FreeProductTorsion.fuchsianSourceAction_gTwo_sq_apply
        (fuchsianSourceAction g₂ z)
    _ = -Real.sqrt 2 - 1 / z := by
      rw [fuchsianSourceAction_g₂_apply]
      have hzs : (z : ℂ) + Real.sqrt 2 ≠ 0 := by
        intro hzero
        have him := congrArg Complex.im hzero
        norm_num at him
        exact z.im_pos.ne' him
      have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp [z.ne_zero, hzs]
      ring_nf
      have hsqrt_sq_complex : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
        exact_mod_cast hsqrt_sq
      rw [hsqrt_sq_complex]
      ring

public theorem gTwo_cube_maps_right_to_left :
    fuchsianSourceAction (g₂ ^ 3) • rightRegion ⊆ leftRegion := by
  rintro _ ⟨z, hz, rfl⟩
  change 0 < z.re at hz
  change (fuchsianSourceAction (g₂ ^ 3) • z).re < 0
  have hre := congrArg Complex.re (gTwo_cube_apply z)
  norm_num [Complex.div_re] at hre
  rw [map_pow]
  change ((fuchsianTwoPerm ^ 3) z).re < 0
  rw [hre]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hnorm : 0 < Complex.normSq (z : ℂ) := z.normSq_pos
  have hquot : 0 < z.re / Complex.normSq (z : ℂ) := div_pos hz hnorm
  linarith

/-- Every nonidentity element of the order-three factor moves the left region right. -/
public theorem inl_maps_left_to_right (a : CyclicThree) (ha : a ≠ 1) :
    fuchsianSourceAction (Monoid.Coprod.inl a) • leftRegion ⊆ rightRegion := by
  fin_cases a
  · exact (ha rfl).elim
  · change fuchsianSourceAction g₁ • leftRegion ⊆ rightRegion
    exact gOne_maps_left_to_right
  · change fuchsianSourceAction
      (Monoid.Coprod.inl (Multiplicative.ofAdd (2 : ZMod 3))) • leftRegion ⊆ rightRegion
    rw [show Monoid.Coprod.inl (Multiplicative.ofAdd (2 : ZMod 3)) = g₁ ^ 2 by
      unfold g₁
      rw [pow_two, ← map_mul]
      congr]
    exact gOne_sq_maps_left_to_right

/-- Every nonidentity element of the order-four factor moves the right region left. -/
public theorem inr_maps_right_to_left (a : CyclicFour) (ha : a ≠ 1) :
    fuchsianSourceAction (Monoid.Coprod.inr a) • rightRegion ⊆ leftRegion := by
  fin_cases a
  · exact (ha rfl).elim
  · change fuchsianSourceAction g₂ • rightRegion ⊆ leftRegion
    exact gTwo_maps_right_to_left
  · change fuchsianSourceAction
      (Monoid.Coprod.inr (Multiplicative.ofAdd (2 : ZMod 4))) • rightRegion ⊆ leftRegion
    rw [show Monoid.Coprod.inr (Multiplicative.ofAdd (2 : ZMod 4)) = g₂ ^ 2 by
      unfold g₂
      rw [pow_two, ← map_mul]
      congr]
    exact gTwo_sq_maps_right_to_left
  · change fuchsianSourceAction
      (Monoid.Coprod.inr (Multiplicative.ofAdd (3 : ZMod 4))) • rightRegion ⊆ leftRegion
    rw [show Monoid.Coprod.inr (Multiplicative.ofAdd (3 : ZMod 4)) = g₂ ^ 3 by
      unfold g₂
      rw [pow_succ, pow_two, ← map_mul, ← map_mul]
      congr]
    exact gTwo_cube_maps_right_to_left

/-- The two factor representations, indexed in the same way as `DeltaFactor`. -/
@[expose] public noncomputable def factorAction :
    ∀ b : Bool, DeltaFactor b →* Equiv.Perm UpperHalfPlane
  | false => cyclicRepresentation 3 fuchsianOnePerm fuchsianOnePerm_pow_three
  | true => cyclicRepresentation 4 fuchsianTwoPerm fuchsianTwoPerm_pow_four

@[simp]
public theorem factorAction_false (a : CyclicThree) :
    factorAction false a = fuchsianSourceAction (Monoid.Coprod.inl a) :=
  rfl

@[simp]
public theorem factorAction_true (a : CyclicFour) :
    factorAction true a = fuchsianSourceAction (Monoid.Coprod.inr a) :=
  rfl

/-- The right region belongs to the order-three factor and the left region to the order-four
factor. -/
@[expose] public def pingPongRegion : Bool → Set UpperHalfPlane
  | false => rightRegion
  | true => leftRegion

public theorem pingPongRegion_nonempty (b : Bool) : (pingPongRegion b).Nonempty := by
  cases b
  · refine ⟨⟨⟨1, 1⟩, by norm_num⟩, ?_⟩
    change (0 : ℝ) < 1
    norm_num
  · refine ⟨⟨⟨-1, 1⟩, by norm_num⟩, ?_⟩
    change (-1 : ℝ) < 0
    norm_num

public theorem pingPongRegion_pairwise_disjoint :
    Pairwise (Disjoint on pingPongRegion) := by
  intro i j hij
  cases i <;> cases j
  · exact (hij rfl).elim
  · change Disjoint rightRegion leftRegion
    rw [Set.disjoint_left]
    intro z hzRight hzLeft
    change 0 < z.re at hzRight
    change z.re < 0 at hzLeft
    linarith
  · change Disjoint leftRegion rightRegion
    rw [Set.disjoint_left]
    intro z hzLeft hzRight
    change z.re < 0 at hzLeft
    change 0 < z.re at hzRight
    linarith
  · exact (hij rfl).elim

public theorem factorAction_ping_pong :
    Pairwise fun i j ↦ ∀ h : DeltaFactor i, h ≠ 1 →
      factorAction i h • pingPongRegion j ⊆ pingPongRegion i := by
  intro i j hij
  cases i <;> cases j
  · exact (hij rfl).elim
  · intro h hh
    change fuchsianSourceAction (Monoid.Coprod.inl h) • leftRegion ⊆ rightRegion
    exact inl_maps_left_to_right h hh
  · intro h hh
    change fuchsianSourceAction (Monoid.Coprod.inr h) • rightRegion ⊆ leftRegion
    exact inr_maps_right_to_left h hh
  · exact (hij rfl).elim

public theorem factor_cardinality :
    3 ≤ #Bool ∨ ∃ i : Bool, 3 ≤ #(DeltaFactor i) := by
  right
  refine ⟨false, ?_⟩
  norm_num [DeltaFactor]

/-- The indexed free-product representation is faithful by the concrete half-plane ping-pong
regions. -/
public theorem indexedFactorAction_injective :
    Function.Injective (Monoid.CoprodI.lift factorAction) := by
  apply Monoid.CoprodI.lift_injective_of_ping_pong factorAction factor_cardinality pingPongRegion
  · exact pingPongRegion_nonempty
  · exact pingPongRegion_pairwise_disjoint
  · exact factorAction_ping_pong

public theorem fuchsianSourceAction_eq_indexed :
    fuchsianSourceAction = (Monoid.CoprodI.lift factorAction).comp deltaToIndexed := by
  apply Monoid.Coprod.hom_ext
  · apply MonoidHom.ext
    intro a
    rfl
  · apply MonoidHom.ext
    intro a
    rfl

/-- The explicit Fuchsian action of `Delta = C₃ * C₄` is faithful. -/
public theorem fuchsianSourceAction_injective : Function.Injective fuchsianSourceAction := by
  rw [fuchsianSourceAction_eq_indexed]
  exact indexedFactorAction_injective.comp deltaIndexedEquiv.injective

end SphereSixComplex.TriangleGroup.FuchsianPingPong
