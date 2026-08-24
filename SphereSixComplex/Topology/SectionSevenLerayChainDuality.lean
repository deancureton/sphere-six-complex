module

public import SphereSixComplex.Topology.SectionSevenLerayDuality

/-!
# Chain-level self-duality of the finite Leray model

This file reverses and transposes every displayed boundary of the finite Leray model.  The
degree-complement maps use the same unimodular matrices as
`SectionSevenLerayAlgebraicDuality`.  Their chain-map equation is equivalent to the single integer
identity `top = -sign`.  Algebraic duality supplies that identity, so the complement maps assemble
to an isomorphism of chain complexes.

Everything here concerns finite free abelian groups.  No singular chains or topological
Poincaré-duality theorem is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Matrix

namespace SphereSixComplex

/-- The transpose of the unresolved degree-five boundary. -/
public def sectionSevenReversedBoundaryTwo (top : ℤ) :
    (Fin 2 → ℤ) →+ (Fin 1 → ℤ) where
  toFun x := ![top * x 1]
  map_zero' := by
    funext i
    fin_cases i
    simp
  map_add' x y := by
    funext i
    fin_cases i
    simp
    ring

/-- The transpose of the displayed degree-four boundary. -/
public def sectionSevenReversedBoundaryThree :
    (Fin 2 → ℤ) →+ (Fin 2 → ℤ) where
  toFun x := ![-x 1, 0]
  map_zero' := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    abel

/-- The transpose of the displayed degree-three boundary. -/
public def sectionSevenReversedBoundaryFour :
    (Fin 2 → ℤ) →+ (Fin 2 → ℤ) :=
  sectionSevenReversedBoundaryThree

/-- The transpose of the displayed degree-two boundary. -/
public def sectionSevenReversedBoundaryFive :
    (Fin 1 → ℤ) →+ (Fin 2 → ℤ) where
  toFun x := ![-x 0, 0]
  map_zero' := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp
    abel

/-- All boundaries of the reversed-transpose complex. -/
public def sectionSevenReversedBoundary (top : ℤ) :
    ∀ n, SectionSevenLerayGroup n.succ →+ SectionSevenLerayGroup n
  | 0 => 0
  | 1 => sectionSevenReversedBoundaryTwo top
  | 2 => sectionSevenReversedBoundaryThree
  | 3 => sectionSevenReversedBoundaryFour
  | 4 => sectionSevenReversedBoundaryFive
  | 5 => 0
  | 6 => 0
  | _ + 7 => 0

private theorem sectionSevenReversedBoundaryTwo_comp_three (top : ℤ) :
    (sectionSevenReversedBoundaryTwo top).comp sectionSevenReversedBoundaryThree = 0 := by
  apply AddMonoidHom.ext
  intro x
  funext i
  fin_cases i
  simp [sectionSevenReversedBoundaryTwo, sectionSevenReversedBoundaryThree]

private theorem sectionSevenReversedBoundaryThree_comp_four :
    sectionSevenReversedBoundaryThree.comp sectionSevenReversedBoundaryFour = 0 := by
  apply AddMonoidHom.ext
  intro x
  funext i
  fin_cases i <;>
    rfl

private theorem sectionSevenReversedBoundaryFour_comp_five :
    sectionSevenReversedBoundaryFour.comp sectionSevenReversedBoundaryFive = 0 := by
  apply AddMonoidHom.ext
  intro x
  funext i
  fin_cases i <;>
    rfl

public theorem sectionSevenReversedBoundary_comp (top : ℤ) (n : ℕ) :
    (sectionSevenReversedBoundary top n).comp
      (sectionSevenReversedBoundary top n.succ) = 0 := by
  rcases n with (_ | _ | _ | _ | _ | _ | _ | n)
  · rfl
  · exact sectionSevenReversedBoundaryTwo_comp_three top
  · exact sectionSevenReversedBoundaryThree_comp_four
  · exact sectionSevenReversedBoundaryFour_comp_five
  · apply AddMonoidHom.ext
    intro x
    exact sectionSevenReversedBoundaryFive.map_zero
  · rfl
  · rfl
  · rfl

/-- The chain complex obtained by reversing degrees around six and transposing the finite model's
boundary matrices. -/
public def sectionSevenReversedDualChainModel (top : ℤ) :
    ChainComplex AddCommGrpCat ℕ :=
  ChainComplex.of
    (fun n ↦ AddCommGrpCat.of (SectionSevenLerayGroup n))
    (fun n ↦ AddCommGrpCat.ofHom (sectionSevenReversedBoundary top n))
    (by
      intro n
      apply AddCommGrpCat.hom_ext
      exact sectionSevenReversedBoundary_comp top n)

/-- Multiplication by the orientation sign on a rank-one free abelian group. -/
public def sectionSevenSignRankOneHom (sign : ℤ) :
    (Fin 1 → ℤ) →+ (Fin 1 → ℤ) where
  toFun x := ![sign * x 0]
  map_zero' := by
    funext i
    fin_cases i
    simp
  map_add' x y := by
    funext i
    fin_cases i
    simp
    ring

/-- The hyperbolic swap on a rank-two free abelian group. -/
public def sectionSevenSwapRankTwoHom : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) where
  toFun x := ![x 1, x 0]
  map_zero' := by
    funext i
    fin_cases i <;>
      simp
  map_add' x y := by
    funext i
    fin_cases i <;>
      simp

/-- The degree-complement homomorphism: identity in degrees zero and six, the orientation sign in
degrees one and five, and the hyperbolic swap in degrees two through four. -/
public def sectionSevenDegreeComplementHom (sign : ℤ) :
    ∀ n, SectionSevenLerayGroup n →+ SectionSevenLerayGroup n
  | 0 => AddMonoidHom.id _
  | 1 => sectionSevenSignRankOneHom sign
  | 2 => sectionSevenSwapRankTwoHom
  | 3 => sectionSevenSwapRankTwoHom
  | 4 => sectionSevenSwapRankTwoHom
  | 5 => sectionSevenSignRankOneHom sign
  | 6 => AddMonoidHom.id _
  | _ + 7 => AddMonoidHom.id _

/-- The pointwise chain-map equation for the explicit degree-complement homomorphisms. -/
public def SectionSevenDegreeComplementCompatible (top sign : ℤ) : Prop :=
  ∀ n : ℕ,
    (sectionSevenReversedBoundary top n).comp (sectionSevenDegreeComplementHom sign n.succ) =
      (sectionSevenDegreeComplementHom sign n).comp (sectionSevenLerayBoundary top n)

/-- Chain compatibility of the complement maps is exactly the unresolved unit equation. -/
public theorem sectionSevenDegreeComplementCompatible_iff
    (top sign : ℤ) :
    SectionSevenDegreeComplementCompatible top sign ↔ top = -sign := by
  constructor
  · intro h
    have hdegreeOne :
        (sectionSevenReversedBoundaryTwo top).comp sectionSevenSwapRankTwoHom =
          (sectionSevenSignRankOneHom sign).comp sectionSevenLerayBoundaryTwo := by
      have hdegreeOne' := h 1
      change (sectionSevenReversedBoundaryTwo top).comp sectionSevenSwapRankTwoHom =
        (sectionSevenSignRankOneHom sign).comp sectionSevenLerayBoundaryTwo at hdegreeOne'
      exact hdegreeOne'
    have heq := DFunLike.congr_fun hdegreeOne ![1, 0]
    have hcoord := congrFun heq 0
    simpa [sectionSevenReversedBoundaryTwo, sectionSevenSignRankOneHom,
      sectionSevenSwapRankTwoHom,
      sectionSevenLerayBoundaryTwo, chosenLerayDifferential, twistObstruction] using hcoord
  · intro htop n
    rcases n with (_ | _ | _ | _ | _ | _ | _ | n)
    · change (0 : (Fin 1 → ℤ) →+ (Fin 1 → ℤ)).comp (sectionSevenSignRankOneHom sign) =
        (AddMonoidHom.id _).comp 0
      rfl
    · change (sectionSevenReversedBoundaryTwo top).comp sectionSevenSwapRankTwoHom =
        (sectionSevenSignRankOneHom sign).comp sectionSevenLerayBoundaryTwo
      apply AddMonoidHom.ext
      intro x
      funext i
      fin_cases i
      simp [sectionSevenReversedBoundaryTwo, sectionSevenSwapRankTwoHom,
        sectionSevenSignRankOneHom, sectionSevenLerayBoundaryTwo, chosenLerayDifferential,
        twistObstruction, htop]
    · change sectionSevenReversedBoundaryThree.comp sectionSevenSwapRankTwoHom =
        sectionSevenSwapRankTwoHom.comp sectionSevenLerayBoundaryThree
      apply AddMonoidHom.ext
      intro x
      funext i
      fin_cases i <;>
        simp [sectionSevenReversedBoundaryThree, sectionSevenSwapRankTwoHom,
          sectionSevenLerayBoundaryThree, chosenLerayDifferential, twistObstruction]
    · change sectionSevenReversedBoundaryFour.comp sectionSevenSwapRankTwoHom =
        sectionSevenSwapRankTwoHom.comp sectionSevenLerayBoundaryFour
      apply AddMonoidHom.ext
      intro x
      funext i
      fin_cases i <;>
        simp [sectionSevenReversedBoundaryFour, sectionSevenReversedBoundaryThree,
          sectionSevenSwapRankTwoHom, sectionSevenLerayBoundaryFour,
          chosenLerayDifferential, twistObstruction]
    · change sectionSevenReversedBoundaryFive.comp (sectionSevenSignRankOneHom sign) =
        sectionSevenSwapRankTwoHom.comp (sectionSevenLerayBoundaryFive top)
      apply AddMonoidHom.ext
      intro x
      funext i
      fin_cases i <;>
        simp [sectionSevenReversedBoundaryFive, sectionSevenSignRankOneHom,
          sectionSevenSwapRankTwoHom, sectionSevenLerayBoundaryFive, htop]
    · change (0 : (Fin 1 → ℤ) →+ (Fin 1 → ℤ)).comp (AddMonoidHom.id _) =
        (sectionSevenSignRankOneHom sign).comp 0
      apply AddMonoidHom.ext
      intro x
      funext i
      fin_cases i
      simp [sectionSevenSignRankOneHom]
    · rfl
    · rfl

/-- A signed degree-complement chain map exists exactly when the unresolved coefficient is a unit
of `ℤ`. -/
public theorem exists_sectionSevenDegreeComplementCompatible_iff (top : ℤ) :
    (∃ sign : ℤ, (sign = 1 ∨ sign = -1) ∧
      SectionSevenDegreeComplementCompatible top sign) ↔ top = 1 ∨ top = -1 := by
  constructor
  · rintro ⟨sign, hsign, hcompatible⟩
    have htop := (sectionSevenDegreeComplementCompatible_iff top sign).mp hcompatible
    rcases hsign with rfl | rfl
    · right
      simpa using htop
    · left
      simpa using htop
  · intro htop
    rcases htop with rfl | rfl
    · refine ⟨-1, Or.inr rfl, ?_⟩
      exact (sectionSevenDegreeComplementCompatible_iff 1 (-1)).mpr (by norm_num)
    · refine ⟨1, Or.inl rfl, ?_⟩
      exact (sectionSevenDegreeComplementCompatible_iff (-1) 1).mpr (by norm_num)

/-- The adjointness equation determines the coefficient together with its orientation sign. -/
public theorem SectionSevenLerayAlgebraicDuality.top_eq_neg_sign
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) :
    top = -h.sign := by
  have hadj := h.boundary_adjoint ![1, 0] ![1]
  simp [sectionSevenOneFivePairing, sectionSevenTwoFourPairing,
    sectionSevenOneFivePairingMatrix, sectionSevenTwoFourPairingMatrix,
    sectionSevenLerayBoundaryTwo, sectionSevenLerayBoundaryFive,
    chosenLerayDifferential, twistObstruction, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at hadj
  rcases h.sign_eq_one_or_neg_one with hs | hs
  · simp [hs] at hadj ⊢
    omega
  · simp [hs] at hadj ⊢
    omega

/-- A unit sign acts invertibly on the rank-one lattice. -/
public def sectionSevenSignRankOneAddEquiv (sign : ℤ) (hsign : sign = 1 ∨ sign = -1) :
    (Fin 1 → ℤ) ≃+ (Fin 1 → ℤ) where
  toFun := sectionSevenSignRankOneHom sign
  invFun := sectionSevenSignRankOneHom sign
  left_inv x := by
    rcases hsign with rfl | rfl
    · funext i
      fin_cases i
      simp [sectionSevenSignRankOneHom]
    · funext i
      fin_cases i
      simp [sectionSevenSignRankOneHom]
  right_inv x := by
    rcases hsign with rfl | rfl
    · funext i
      fin_cases i
      simp [sectionSevenSignRankOneHom]
    · funext i
      fin_cases i
      simp [sectionSevenSignRankOneHom]
  map_add' := (sectionSevenSignRankOneHom sign).map_add

/-- The hyperbolic swap is a self-inverse additive equivalence. -/
public def sectionSevenSwapRankTwoAddEquiv : (Fin 2 → ℤ) ≃+ (Fin 2 → ℤ) where
  toFun := sectionSevenSwapRankTwoHom
  invFun := sectionSevenSwapRankTwoHom
  left_inv x := by
    funext i
    fin_cases i <;>
      rfl
  right_inv x := by
    funext i
    fin_cases i <;>
      rfl
  map_add' := sectionSevenSwapRankTwoHom.map_add

/-- The degreewise additive equivalences underlying chain-level duality. -/
public def sectionSevenDegreeComplementAddEquiv (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) :
    ∀ n, SectionSevenLerayGroup n ≃+ SectionSevenLerayGroup n
  | 0 => AddEquiv.refl _
  | 1 => sectionSevenSignRankOneAddEquiv sign hsign
  | 2 => sectionSevenSwapRankTwoAddEquiv
  | 3 => sectionSevenSwapRankTwoAddEquiv
  | 4 => sectionSevenSwapRankTwoAddEquiv
  | 5 => sectionSevenSignRankOneAddEquiv sign hsign
  | 6 => AddEquiv.refl _
  | _ + 7 => AddEquiv.refl _

@[simp]
public theorem sectionSevenDegreeComplementAddEquiv_toAddMonoidHom (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) (n : ℕ) :
    (sectionSevenDegreeComplementAddEquiv sign hsign n).toAddMonoidHom =
      sectionSevenDegreeComplementHom sign n := by
  rcases n with (_ | _ | _ | _ | _ | _ | _ | n) <;>
    rfl

/-- The component isomorphism used in the chain-level self-duality. -/
public def sectionSevenDegreeComplementIso (top sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) (n : ℕ) :
    (sectionSevenLerayChainModel top).X n ≅ (sectionSevenReversedDualChainModel top).X n :=
  (sectionSevenDegreeComplementAddEquiv sign hsign n).toAddCommGrpIso

/-- Algebraic duality upgrades the complementary perfect pairings to an isomorphism from the
finite Leray chain model to its reversed transpose. -/
public noncomputable def SectionSevenLerayAlgebraicDuality.chainSelfDualityIso
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) :
    sectionSevenLerayChainModel top ≅ sectionSevenReversedDualChainModel top :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ sectionSevenDegreeComplementIso top h.sign h.sign_eq_one_or_neg_one n)
    (by
      intro i j hij
      simp only [ComplexShape.down_Rel] at hij
      rcases hij with rfl
      apply AddCommGrpCat.hom_ext
      have hcompatible : SectionSevenDegreeComplementCompatible top h.sign :=
        (sectionSevenDegreeComplementCompatible_iff top h.sign).mpr h.top_eq_neg_sign
      simp only [sectionSevenDegreeComplementIso, sectionSevenLerayChainModel,
        sectionSevenReversedDualChainModel, ChainComplex.of_d,
        AddEquiv.toAddCommGrpIso_hom, AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom,
        sectionSevenDegreeComplementAddEquiv_toAddMonoidHom]
      exact (hcompatible j))

end SphereSixComplex
