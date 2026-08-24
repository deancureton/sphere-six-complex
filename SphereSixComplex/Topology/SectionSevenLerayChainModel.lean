module

public import SphereSixComplex.Topology.HomologyComputation
public import SphereSixComplex.Topology.MayerVietoris
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# The three-differential Leray chain model from Section 7

Proposition 7.27 identifies three rank-one cohomological Leray differentials, with one common sign,
as multiplication by the obstruction `p`.  For the chosen twists, `p = -1`.  Taking integral
transposes and totalizing just these three arrows gives the chain groups of ranks

`1, 1, 2, 2, 2, 1, 1`

in degrees zero through six.  The bottom and top rank-one groups record the two edge survivors.
The paper does not compute the fourth possible differential from total degree four to five; it
uses Poincaré duality instead.  The model therefore has an explicit integer parameter `top` for
that missing coefficient.  This file proves unconditional vanishing in degrees one through three,
vanishing in degrees four and five when `top = ±1`, and infinite-cyclic homology in degree six.

This is the integral dual of the algebraic `d₂` model, not a claimed cellular chain complex of the
glued space.  Passing from it to actual singular homology requires convergence and filtration
identifications for the integral Leray spectral sequence, universal-coefficient identifications,
or a degreewise chain comparison.  Mathlib currently provides neither the required topological
Leray spectral sequence nor Poincaré--Lefschetz duality.  The final theorems therefore accept an
explicit chain map and an honest degreewise homology-isomorphism instance.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Matrix

namespace SphereSixComplex

/-- Ranks of the totalized Section 7 Leray model in each chain degree. -/
public def sectionSevenLerayRank : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 1
  | 6 => 1
  | _ => 0

/-- The free integral group in degree `n` of the Leray model. -/
public abbrev SectionSevenLerayGroup (n : ℕ) :=
  Fin (sectionSevenLerayRank n) → ℤ

/-- The first of the three totalized Leray differentials. -/
public def sectionSevenLerayBoundaryTwo : (Fin 2 → ℤ) →+ (Fin 1 → ℤ) where
  toFun x := ![chosenLerayDifferential 1 (x 0)]
  map_zero' := by
    funext i
    fin_cases i
    norm_num [chosenLerayDifferential, twistObstruction]
  map_add' x y := by
    funext i
    fin_cases i
    simp [chosenLerayDifferential, twistObstruction]
    abel

/-- The middle totalized Leray differential, landing in the complementary summand. -/
public def sectionSevenLerayBoundaryThree : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) where
  toFun x := ![0, chosenLerayDifferential 1 (x 0)]
  map_zero' := by
    funext i
    fin_cases i <;> norm_num [chosenLerayDifferential, twistObstruction]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [chosenLerayDifferential, twistObstruction]
    abel

/-- The last of the three totalized Leray differentials. -/
public def sectionSevenLerayBoundaryFour : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) where
  toFun x := ![0, chosenLerayDifferential 1 (x 0)]
  map_zero' := by
    funext i
    fin_cases i <;> norm_num [chosenLerayDifferential, twistObstruction]
  map_add' x y := by
    funext i
    fin_cases i <;> simp [chosenLerayDifferential, twistObstruction]
    abel

/-- The uncomputed fourth Leray differential, retained as the honest integer parameter `top`. -/
public def sectionSevenLerayBoundaryFive (top : ℤ) : (Fin 1 → ℤ) →+ (Fin 2 → ℤ) where
  toFun x := ![0, top * x 0]
  map_zero' := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    ring

public theorem sectionSevenLerayBoundaryTwo_comp_three :
    sectionSevenLerayBoundaryTwo.comp sectionSevenLerayBoundaryThree = 0 := by
  apply AddMonoidHom.ext
  intro x
  funext i
  fin_cases i
  rfl

public theorem sectionSevenLerayBoundaryThree_comp_four :
    sectionSevenLerayBoundaryThree.comp sectionSevenLerayBoundaryFour = 0 := by
  apply AddMonoidHom.ext
  intro x
  funext i
  fin_cases i <;> rfl

public theorem sectionSevenLerayBoundaryFour_comp_five (top : ℤ) :
    sectionSevenLerayBoundaryFour.comp (sectionSevenLerayBoundaryFive top) = 0 := by
  apply AddMonoidHom.ext
  intro x
  funext i
  fin_cases i <;> rfl

/-- The differential in every degree of the totalized Leray model. -/
public def sectionSevenLerayBoundary (top : ℤ) :
    ∀ n, SectionSevenLerayGroup n.succ →+ SectionSevenLerayGroup n
  | 0 => 0
  | 1 => sectionSevenLerayBoundaryTwo
  | 2 => sectionSevenLerayBoundaryThree
  | 3 => sectionSevenLerayBoundaryFour
  | 4 => sectionSevenLerayBoundaryFive top
  | 5 => 0
  | 6 => 0
  | _ + 7 => 0

public theorem sectionSevenLerayBoundary_comp (top : ℤ) (n : ℕ) :
    (sectionSevenLerayBoundary top n).comp (sectionSevenLerayBoundary top n.succ) = 0 := by
  rcases n with (_ | _ | _ | _ | _ | _ | _ | n)
  · rfl
  · exact sectionSevenLerayBoundaryTwo_comp_three
  · exact sectionSevenLerayBoundaryThree_comp_four
  · exact sectionSevenLerayBoundaryFour_comp_five top
  · apply AddMonoidHom.ext
    intro x
    change sectionSevenLerayBoundaryFive top (0 : Fin 1 → ℤ) = 0
    exact (sectionSevenLerayBoundaryFive top).map_zero
  · rfl
  · rfl
  · rfl

/-- The finite chain complex obtained by totalizing the three explicit Leray differentials and
retaining the bottom and top edge survivors. -/
public def sectionSevenLerayChainModel (top : ℤ) : ChainComplex AddCommGrpCat ℕ :=
  ChainComplex.of
    (fun n ↦ AddCommGrpCat.of (SectionSevenLerayGroup n))
    (fun n ↦ AddCommGrpCat.ofHom (sectionSevenLerayBoundary top n))
    (by
      intro n
      apply AddCommGrpCat.hom_ext
      exact sectionSevenLerayBoundary_comp top n)

/-- The totalized Leray model is exact in degree one. -/
public theorem sectionSevenLerayChainModel_exactAt_one (top : ℤ) :
    (sectionSevenLerayChainModel top).ExactAt 1 := by
  let S := (sectionSevenLerayChainModel top).sc' 2 1 0
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff_function_exact]
    change Function.Exact sectionSevenLerayBoundaryTwo
      (0 : (Fin 1 → ℤ) →+ (Fin 1 → ℤ))
    intro y
    constructor
    · intro _
      refine ⟨![-y 0, 0], ?_⟩
      funext i
      fin_cases i
      simp [sectionSevenLerayBoundaryTwo, chosenLerayDifferential, twistObstruction]
    · rintro ⟨z, rfl⟩
      simp
  rw [(sectionSevenLerayChainModel top).exactAt_iff]
  apply ShortComplex.exact_of_iso
    ((sectionSevenLerayChainModel top).isoSc' 2 1 0
      ((ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk 2 1 (by omega)))
      ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 1 0 (by omega)))).symm
  exact hS

/-- The totalized Leray model is exact in degree two. -/
public theorem sectionSevenLerayChainModel_exactAt_two (top : ℤ) :
    (sectionSevenLerayChainModel top).ExactAt 2 := by
  let S := (sectionSevenLerayChainModel top).sc' 3 2 1
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff_function_exact]
    change Function.Exact sectionSevenLerayBoundaryThree sectionSevenLerayBoundaryTwo
    intro y
    constructor
    · intro hy
      have hy0 : y 0 = 0 := by
        have h := congrFun hy 0
        simpa [sectionSevenLerayBoundaryTwo, chosenLerayDifferential, twistObstruction] using h
      refine ⟨![-y 1, 0], ?_⟩
      funext i
      fin_cases i <;>
        simp [sectionSevenLerayBoundaryThree, chosenLerayDifferential, twistObstruction, hy0]
    · rintro ⟨z, rfl⟩
      exact DFunLike.congr_fun sectionSevenLerayBoundaryTwo_comp_three z
  rw [(sectionSevenLerayChainModel top).exactAt_iff]
  apply ShortComplex.exact_of_iso
    ((sectionSevenLerayChainModel top).isoSc' 3 2 1
      ((ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk 3 2 (by omega)))
      ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 2 1 (by omega)))).symm
  exact hS

/-- The totalized Leray model is exact in degree three. -/
public theorem sectionSevenLerayChainModel_exactAt_three (top : ℤ) :
    (sectionSevenLerayChainModel top).ExactAt 3 := by
  let S := (sectionSevenLerayChainModel top).sc' 4 3 2
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff_function_exact]
    change Function.Exact sectionSevenLerayBoundaryFour sectionSevenLerayBoundaryThree
    intro y
    constructor
    · intro hy
      have hy0 : y 0 = 0 := by
        have h := congrFun hy 1
        simpa [sectionSevenLerayBoundaryThree, chosenLerayDifferential, twistObstruction] using h
      refine ⟨![-y 1, 0], ?_⟩
      funext i
      fin_cases i <;>
        simp [sectionSevenLerayBoundaryFour, chosenLerayDifferential, twistObstruction, hy0]
    · rintro ⟨z, rfl⟩
      exact DFunLike.congr_fun sectionSevenLerayBoundaryThree_comp_four z
  rw [(sectionSevenLerayChainModel top).exactAt_iff]
  apply ShortComplex.exact_of_iso
    ((sectionSevenLerayChainModel top).isoSc' 4 3 2
      ((ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk 4 3 (by omega)))
      ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 3 2 (by omega)))).symm
  exact hS

/-- A unit value of the missing top coefficient makes the model exact in degree four. -/
public theorem sectionSevenLerayChainModel_exactAt_four (top : ℤ)
    (htop : top = 1 ∨ top = -1) :
    (sectionSevenLerayChainModel top).ExactAt 4 := by
  let S := (sectionSevenLerayChainModel top).sc' 5 4 3
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff_function_exact]
    change Function.Exact (sectionSevenLerayBoundaryFive top) sectionSevenLerayBoundaryFour
    intro y
    constructor
    · intro hy
      have hy0 : y 0 = 0 := by
        have h := congrFun hy 1
        simpa [sectionSevenLerayBoundaryFour, chosenLerayDifferential, twistObstruction] using h
      have hsurj : Function.Surjective (fun z : ℤ ↦ top * z) := by
        rcases htop with rfl | rfl
        · intro z
          exact ⟨z, by simp⟩
        · intro z
          exact ⟨-z, by simp⟩
      obtain ⟨z, hz⟩ := hsurj (y 1)
      refine ⟨![z], ?_⟩
      funext i
      fin_cases i <;> simp [sectionSevenLerayBoundaryFive, hy0, hz]
    · rintro ⟨z, rfl⟩
      funext i
      fin_cases i <;>
        simp [sectionSevenLerayBoundaryFour, sectionSevenLerayBoundaryFive,
          chosenLerayDifferential, twistObstruction]
  rw [(sectionSevenLerayChainModel top).exactAt_iff]
  apply ShortComplex.exact_of_iso
    ((sectionSevenLerayChainModel top).isoSc' 5 4 3
      ((ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk 5 4 (by omega)))
      ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 4 3 (by omega)))).symm
  exact hS

/-- A unit value of the missing top coefficient makes the model exact in degree five. -/
public theorem sectionSevenLerayChainModel_exactAt_five (top : ℤ)
    (htop : top = 1 ∨ top = -1) :
    (sectionSevenLerayChainModel top).ExactAt 5 := by
  let S := (sectionSevenLerayChainModel top).sc' 6 5 4
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff_function_exact]
    change Function.Exact (0 : (Fin 1 → ℤ) →+ (Fin 1 → ℤ))
      (sectionSevenLerayBoundaryFive top)
    intro y
    constructor
    · intro hy
      have hcoord : top * y 0 = 0 := by
        have h := congrFun hy 1
        simpa [sectionSevenLerayBoundaryFive] using h
      have htop0 : top ≠ 0 := by
        rcases htop with rfl | rfl <;> norm_num
      have hy0 : y 0 = 0 := (mul_eq_zero.mp hcoord).resolve_left htop0
      refine ⟨0, ?_⟩
      funext i
      fin_cases i
      simp [hy0]
    · rintro ⟨z, rfl⟩
      simp
  rw [(sectionSevenLerayChainModel top).exactAt_iff]
  apply ShortComplex.exact_of_iso
    ((sectionSevenLerayChainModel top).isoSc' 6 5 4
      ((ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk 6 5 (by omega)))
      ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 5 4 (by omega)))).symm
  exact hS

public theorem sectionSevenLerayChainModel_homology_one_isZero (top : ℤ) :
    IsZero ((sectionSevenLerayChainModel top).homology 1) :=
  (sectionSevenLerayChainModel_exactAt_one top).isZero_homology

public theorem sectionSevenLerayChainModel_homology_two_isZero (top : ℤ) :
    IsZero ((sectionSevenLerayChainModel top).homology 2) :=
  (sectionSevenLerayChainModel_exactAt_two top).isZero_homology

public theorem sectionSevenLerayChainModel_homology_three_isZero (top : ℤ) :
    IsZero ((sectionSevenLerayChainModel top).homology 3) :=
  (sectionSevenLerayChainModel_exactAt_three top).isZero_homology

public theorem sectionSevenLerayChainModel_homology_four_isZero (top : ℤ)
    (htop : top = 1 ∨ top = -1) :
    IsZero ((sectionSevenLerayChainModel top).homology 4) :=
  (sectionSevenLerayChainModel_exactAt_four top htop).isZero_homology

public theorem sectionSevenLerayChainModel_homology_five_isZero (top : ℤ)
    (htop : top = 1 ∨ top = -1) :
    IsZero ((sectionSevenLerayChainModel top).homology 5) :=
  (sectionSevenLerayChainModel_exactAt_five top htop).isZero_homology

/-- Every middle-degree homology object of the Leray model is zero. -/
public theorem sectionSevenLerayChainModel_middle_homology_isZero (top : ℤ)
    (htop : top = 1 ∨ top = -1) (k : ℕ)
    (h1 : 1 ≤ k) (h5 : k ≤ 5) :
    IsZero ((sectionSevenLerayChainModel top).homology k) := by
  interval_cases k
  · exact sectionSevenLerayChainModel_homology_one_isZero top
  · exact sectionSevenLerayChainModel_homology_two_isZero top
  · exact sectionSevenLerayChainModel_homology_three_isZero top
  · exact sectionSevenLerayChainModel_homology_four_isZero top htop
  · exact sectionSevenLerayChainModel_homology_five_isZero top htop

/-- Evaluation is the canonical additive equivalence from a rank-one function group to `ℤ`. -/
public def finOneIntegerAddEquiv : (Fin 1 → ℤ) ≃+ ℤ where
  toFun x := x 0
  invFun z := ![z]
  left_inv x := by
    funext i
    fin_cases i
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The top homology of the finite Leray model is infinite cyclic. -/
public noncomputable def sectionSevenLerayChainModel_homology_six_equiv (top : ℤ) :
    (sectionSevenLerayChainModel top).homology 6 ≃+ ℤ := by
  let S := (sectionSevenLerayChainModel top).sc' 7 6 5
  have hf : S.f = 0 := by rfl
  have hg : S.g = 0 := by rfl
  let h := ShortComplex.HomologyData.ofZeros S hf hg
  exact
    ((ShortComplex.homologyMapIso
      ((sectionSevenLerayChainModel top).isoSc' 7 6 5
        ((ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk 7 6 (by omega)))
        ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 6 5 (by omega))))).trans
      h.left.homologyIso).addCommGroupIsoToAddEquiv.trans finOneIntegerAddEquiv

/-- A degreewise chain comparison transfers the model's middle-degree vanishing to actual integral
singular homology. -/
public theorem integralSingularHomology_middle_subsingleton_of_sectionSevenLerayComparison
    {X : Type} [TopologicalSpace X] (top : ℤ) (htop : top = 1 ∨ top = -1)
    (k : ℕ) (h1 : 1 ≤ k) (h5 : k ≤ 5)
    (f : sectionSevenLerayChainModel top ⟶ IntegralSingularChainComplex X)
    [IsIso ((sectionSevenLerayChainModel top).homologyMap f k)] :
    Subsingleton (IntegralSingularHomology k X) := by
  have hSingular : IsZero ((IntegralSingularChainComplex X).homology k) :=
    IsZero.of_iso (sectionSevenLerayChainModel_middle_homology_isZero top htop k h1 h5)
      (asIso ((sectionSevenLerayChainModel top).homologyMap f k)).symm
  exact AddCommGrpCat.subsingleton_of_isZero hSingular

/-- A degree-six chain comparison transfers the model's explicit top generator to actual integral
singular homology. -/
public noncomputable def integralSingularHomologySixEquivInteger_of_sectionSevenLerayComparison
    {X : Type} [TopologicalSpace X] (top : ℤ)
    (f : sectionSevenLerayChainModel top ⟶ IntegralSingularChainComplex X)
    [IsIso ((sectionSevenLerayChainModel top).homologyMap f 6)] :
    IntegralSingularHomology 6 X ≃+ ℤ :=
  (asIso ((sectionSevenLerayChainModel top).homologyMap f 6)).symm.addCommGroupIsoToAddEquiv.trans
    (sectionSevenLerayChainModel_homology_six_equiv top)

end SphereSixComplex
