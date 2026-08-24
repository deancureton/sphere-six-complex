module

public import SphereSixComplex.Topology.FundamentalGroup
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The fundamental-group presentation in Section 7

Van Kampen first gives generators `c,x,y`, with `c` central, and relations
`xy=c^ℓ₀`, `x^3=c^ℓ₁`, and `y^4=c^ℓ₂`.  Eliminating `y` leaves the displayed
two-generator integral relation matrix.  The only topological input retained here is the assertion
that the fundamental group of the glued space has this presentation.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex.Topology

/-- The unreduced van Kampen relations displayed in the proof of Theorem 7.17.  The subgroup
`Λtor=ker(M₀-I)=im(M₀-I)` is written in the coordinates computed in `LatticeData` as
`{λ | λ 0 = 0 ∧ λ 1 = 0}`. -/
public structure FullVanKampenRelations (G : Type*) [Group G]
    (v₁ v₂ μ : LatticeData.Lattice) where
  translation : LatticeData.Lattice →+ Additive G
  ρ₁ : G
  ρ₂ : G
  conjugate_one : ∀ a, ρ₁ * Additive.toMul (translation a) * ρ₁⁻¹ =
    Additive.toMul (translation (LatticeData.A₁.mulVec a))
  conjugate_two : ∀ a, ρ₂ * Additive.toMul (translation a) * ρ₂⁻¹ =
    Additive.toMul (translation (LatticeData.A₂.mulVec a))
  elliptic_one : ρ₁ ^ 3 = Additive.toMul (translation v₁)
  elliptic_two : ρ₂ ^ 4 = Additive.toMul (translation v₂)
  cusp : ρ₁ * ρ₂ = Additive.toMul (translation μ)
  toric_vanishes : ∀ a, a 0 = 0 → a 1 = 0 → Additive.toMul (translation a) = 1

/-- The obstruction integer `p=12ℓ₀-4ℓ₁-3ℓ₂`. -/
public def paperObstruction (ℓ₀ ℓ₁ ℓ₂ : ℤ) : ℤ := 12 * ℓ₀ - 4 * ℓ₁ - 3 * ℓ₂

/-- The relation matrix in the ordered exponent basis `(x,c)`.  Its rows encode
`x^3=c^ℓ₁` and, after eliminating `y`, `x^4=c^(4ℓ₀-ℓ₂)`. -/
public def paperRelationMatrix (ℓ₀ ℓ₁ ℓ₂ : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![3, -ℓ₁;
     4, ℓ₂ - 4 * ℓ₀]

@[simp]
public theorem paperRelationMatrix_det (ℓ₀ ℓ₁ ℓ₂ : ℤ) :
    (paperRelationMatrix ℓ₀ ℓ₁ ℓ₂).det = -paperObstruction ℓ₀ ℓ₁ ℓ₂ := by
  simp [paperRelationMatrix, paperObstruction, Matrix.det_fin_two]
  ring

/-- Linear combinations of the rows of the paper's relation matrix. -/
public def paperRelationMap (ℓ₀ ℓ₁ ℓ₂ : ℤ) : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) :=
  { toFun := fun a ↦ ![3 * a 0 + 4 * a 1, -ℓ₁ * a 0 + (ℓ₂ - 4 * ℓ₀) * a 1]
    map_zero' := by ext i; fin_cases i <;> simp
    map_add' := by
      intro x y
      ext i
      fin_cases i <;> simp <;> ring }

public theorem paperRelationMap_eq_transpose_mulVec (ℓ₀ ℓ₁ ℓ₂ : ℤ) (a : Fin 2 → ℤ) :
    paperRelationMap ℓ₀ ℓ₁ ℓ₂ a = (paperRelationMatrix ℓ₀ ℓ₁ ℓ₂).transpose.mulVec a := by
  funext i
  fin_cases i <;>
    simp [paperRelationMap, paperRelationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The primitive quotient coordinate after the Smith operations in the proof of Theorem 7.17. -/
public def paperCyclicClassifier (ℓ₀ ℓ₁ ℓ₂ : ℤ) :
    (Fin 2 → ℤ) →+ ZMod (paperObstruction ℓ₀ ℓ₁ ℓ₂).natAbs where
  toFun z := (z 1 - (ℓ₁ + ℓ₂ - 4 * ℓ₀) * z 0 : ℤ)
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply]
    push_cast
    ring

/-- The relation lattice is exactly the kernel of the cyclic classifier. -/
public theorem paperRelation_iff_classifier_zero (ℓ₀ ℓ₁ ℓ₂ : ℤ) (z : Fin 2 → ℤ) :
    (∃ a : Fin 2 → ℤ, paperRelationMap ℓ₀ ℓ₁ ℓ₂ a = z) ↔
      paperCyclicClassifier ℓ₀ ℓ₁ ℓ₂ z = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    change ((((paperRelationMap ℓ₀ ℓ₁ ℓ₂ a) 1 -
      (ℓ₁ + ℓ₂ - 4 * ℓ₀) * (paperRelationMap ℓ₀ ℓ₁ ℓ₂ a) 0 : ℤ)) :
        ZMod (paperObstruction ℓ₀ ℓ₁ ℓ₂).natAbs) = 0
    rw [show (paperRelationMap ℓ₀ ℓ₁ ℓ₂ a) 1 -
        (ℓ₁ + ℓ₂ - 4 * ℓ₀) * (paperRelationMap ℓ₀ ℓ₁ ℓ₂ a) 0 =
        paperObstruction ℓ₀ ℓ₁ ℓ₂ * (a 0 + a 1) by
      simp [paperRelationMap, paperObstruction]
      ring]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd]
    exact dvd_mul_right _ _
  · intro h
    change (((z 1 - (ℓ₁ + ℓ₂ - 4 * ℓ₀) * z 0 : ℤ)) :
      ZMod (paperObstruction ℓ₀ ℓ₁ ℓ₂).natAbs) = 0 at h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd] at h
    obtain ⟨k, hk⟩ := h
    refine ⟨![-z 0 + 4 * k, z 0 - 3 * k], ?_⟩
    funext i
    fin_cases i <;>
      simp [paperRelationMap] at hk ⊢ <;>
      unfold paperObstruction at hk <;>
      ring_nf at hk ⊢
    all_goals omega

public theorem paperRelation_range_eq_kernel (ℓ₀ ℓ₁ ℓ₂ : ℤ) :
    (paperRelationMap ℓ₀ ℓ₁ ℓ₂).range = (paperCyclicClassifier ℓ₀ ℓ₁ ℓ₂).ker := by
  ext z
  simpa only [AddMonoidHom.mem_range, AddMonoidHom.mem_ker] using
    paperRelation_iff_classifier_zero ℓ₀ ℓ₁ ℓ₂ z

public theorem paperCyclicClassifier_surjective (ℓ₀ ℓ₁ ℓ₂ : ℤ) :
    Function.Surjective (paperCyclicClassifier ℓ₀ ℓ₁ ℓ₂) := by
  intro z
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨![0, a], ?_⟩
  simp [paperCyclicClassifier]

/-- The abelian two-generator presentation obtained from the three original generators by
eliminating `y`.  The preceding range-kernel theorem proves that its denominator is precisely the
row lattice of `paperRelationMatrix`. -/
public abbrev PaperAdditivePresentation (ℓ₀ ℓ₁ ℓ₂ : ℤ) :=
  (Fin 2 → ℤ) ⧸ (paperCyclicClassifier ℓ₀ ℓ₁ ℓ₂).ker

public theorem paperRelation_zero (ℓ₀ ℓ₁ ℓ₂ : ℤ) (a : Fin 2 → ℤ) :
    (QuotientAddGroup.mk (paperRelationMap ℓ₀ ℓ₁ ℓ₂ a) :
      PaperAdditivePresentation ℓ₀ ℓ₁ ℓ₂) = 0 := by
  rw [QuotientAddGroup.eq_zero_iff, ← paperRelation_range_eq_kernel]
  exact ⟨a, rfl⟩

/-- The multiplicative form of the paper's presented fundamental group. -/
public abbrev PaperPresentedGroup (ℓ₀ ℓ₁ ℓ₂ : ℤ) :=
  Multiplicative (PaperAdditivePresentation ℓ₀ ℓ₁ ℓ₂)

/-- Smith reduction of the paper presentation to the cyclic obstruction group. -/
public noncomputable def paperAdditivePresentationEquiv (ℓ₀ ℓ₁ ℓ₂ : ℤ) :
    PaperAdditivePresentation ℓ₀ ℓ₁ ℓ₂ ≃+
      ZMod (paperObstruction ℓ₀ ℓ₁ ℓ₂).natAbs :=
  QuotientAddGroup.quotientKerEquivOfSurjective (paperCyclicClassifier ℓ₀ ℓ₁ ℓ₂)
    (paperCyclicClassifier_surjective ℓ₀ ℓ₁ ℓ₂)

/-- Multiplicative version of the Smith reduction. -/
public noncomputable def paperPresentedGroupEquiv (ℓ₀ ℓ₁ ℓ₂ : ℤ) :
    PaperPresentedGroup ℓ₀ ℓ₁ ℓ₂ ≃*
      Multiplicative (ZMod (paperObstruction ℓ₀ ℓ₁ ℓ₂).natAbs) :=
  AddEquiv.toMultiplicative (paperAdditivePresentationEquiv ℓ₀ ℓ₁ ℓ₂)

/-- The image of the central generator `c` in the additive presentation. -/
public def paperCAdd (ℓ₀ ℓ₁ ℓ₂ : ℤ) : PaperAdditivePresentation ℓ₀ ℓ₁ ℓ₂ :=
  QuotientAddGroup.mk ![0, 1]

/-- The image of the elliptic generator `x` in the additive presentation. -/
public def paperXAdd (ℓ₀ ℓ₁ ℓ₂ : ℤ) : PaperAdditivePresentation ℓ₀ ℓ₁ ℓ₂ :=
  QuotientAddGroup.mk ![1, 0]

/-- The eliminated generator `y=c^ℓ₀x⁻¹`. -/
public def paperYAdd (ℓ₀ ℓ₁ ℓ₂ : ℤ) : PaperAdditivePresentation ℓ₀ ℓ₁ ℓ₂ :=
  ℓ₀ • paperCAdd ℓ₀ ℓ₁ ℓ₂ - paperXAdd ℓ₀ ℓ₁ ℓ₂

@[simp]
public theorem paper_xy_relation_add (ℓ₀ ℓ₁ ℓ₂ : ℤ) :
    paperXAdd ℓ₀ ℓ₁ ℓ₂ + paperYAdd ℓ₀ ℓ₁ ℓ₂ = ℓ₀ • paperCAdd ℓ₀ ℓ₁ ℓ₂ := by
  simp [paperYAdd]

public theorem paper_x_cube_relation_add (ℓ₀ ℓ₁ ℓ₂ : ℤ) :
    (3 : ℤ) • paperXAdd ℓ₀ ℓ₁ ℓ₂ = ℓ₁ • paperCAdd ℓ₀ ℓ₁ ℓ₂ := by
  let q := QuotientAddGroup.mk' (paperCyclicClassifier ℓ₀ ℓ₁ ℓ₂).ker
  have h := paperRelation_zero ℓ₀ ℓ₁ ℓ₂ ![1, 0]
  change q (paperRelationMap ℓ₀ ℓ₁ ℓ₂ ![1, 0]) = 0 at h
  change (3 : ℤ) • q ![1, 0] = ℓ₁ • q ![0, 1]
  rw [← q.map_zsmul, ← q.map_zsmul, ← sub_eq_zero, ← q.map_sub]
  convert h using 1
  apply congrArg q
  funext i
  fin_cases i <;> simp [paperRelationMap]

public theorem paper_x_fourth_relation_add (ℓ₀ ℓ₁ ℓ₂ : ℤ) :
    (4 : ℤ) • paperXAdd ℓ₀ ℓ₁ ℓ₂ = (4 * ℓ₀ - ℓ₂) • paperCAdd ℓ₀ ℓ₁ ℓ₂ := by
  let q := QuotientAddGroup.mk' (paperCyclicClassifier ℓ₀ ℓ₁ ℓ₂).ker
  have h := paperRelation_zero ℓ₀ ℓ₁ ℓ₂ ![0, 1]
  change q (paperRelationMap ℓ₀ ℓ₁ ℓ₂ ![0, 1]) = 0 at h
  change (4 : ℤ) • q ![1, 0] = (4 * ℓ₀ - ℓ₂) • q ![0, 1]
  rw [← q.map_zsmul, ← q.map_zsmul, ← sub_eq_zero, ← q.map_sub]
  convert h using 1
  apply congrArg q
  funext i
  fin_cases i <;> simp [paperRelationMap]

public theorem paper_y_fourth_relation_add (ℓ₀ ℓ₁ ℓ₂ : ℤ) :
    (4 : ℤ) • paperYAdd ℓ₀ ℓ₁ ℓ₂ = ℓ₂ • paperCAdd ℓ₀ ℓ₁ ℓ₂ := by
  calc
    (4 : ℤ) • paperYAdd ℓ₀ ℓ₁ ℓ₂ =
        (4 * ℓ₀) • paperCAdd ℓ₀ ℓ₁ ℓ₂ - (4 : ℤ) • paperXAdd ℓ₀ ℓ₁ ℓ₂ := by
      unfold paperYAdd
      module
    _ = (4 * ℓ₀) • paperCAdd ℓ₀ ℓ₁ ℓ₂ -
        (4 * ℓ₀ - ℓ₂) • paperCAdd ℓ₀ ℓ₁ ℓ₂ := by
      rw [paper_x_fourth_relation_add]
    _ = ℓ₂ • paperCAdd ℓ₀ ℓ₁ ℓ₂ := by module

/-- The complete original three-generator relations, before eliminating `y`. -/
public structure SatisfiesPaperRelations (G : Type*) [Group G] (ℓ₀ ℓ₁ ℓ₂ : ℤ) where
  c : G
  x : G
  y : G
  central_c : ∀ g : G, Commute c g
  xy : x * y = c ^ ℓ₀
  x_cube : x ^ (3 : ℤ) = c ^ ℓ₁
  y_fourth : y ^ (4 : ℤ) = c ^ ℓ₂

/-- The concrete quotient carries exactly the three displayed relations. -/
public def paperPresentedGroupRelations (ℓ₀ ℓ₁ ℓ₂ : ℤ) :
    SatisfiesPaperRelations (PaperPresentedGroup ℓ₀ ℓ₁ ℓ₂) ℓ₀ ℓ₁ ℓ₂ where
  c := Multiplicative.ofAdd (paperCAdd ℓ₀ ℓ₁ ℓ₂)
  x := Multiplicative.ofAdd (paperXAdd ℓ₀ ℓ₁ ℓ₂)
  y := Multiplicative.ofAdd (paperYAdd ℓ₀ ℓ₁ ℓ₂)
  central_c _ := mul_comm _ _
  xy := paper_xy_relation_add ℓ₀ ℓ₁ ℓ₂
  x_cube := paper_x_cube_relation_add ℓ₀ ℓ₁ ℓ₂
  y_fourth := paper_y_fourth_relation_add ℓ₀ ℓ₁ ℓ₂

/-- The relation `xy=c^ℓ₀`, together with centrality of `c`, forces `x` and `y` to commute. -/
public theorem SatisfiesPaperRelations.commute_xy {G : Type*} [Group G]
    {ℓ₀ ℓ₁ ℓ₂ : ℤ} (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) : Commute r.x r.y := by
  have hp : Commute (r.x * r.y) r.x := by
    rw [r.xy]
    exact (r.central_c r.x).zpow_left ℓ₀
  have h : r.x * (r.y * r.x) = r.x * (r.x * r.y) := by
    simpa only [mul_assoc] using hp.eq
  exact (mul_left_cancel h).symm

/-- After eliminating `y`, its fourth-power relation becomes the second row of
`paperRelationMatrix`. -/
public theorem SatisfiesPaperRelations.x_fourth {G : Type*} [Group G]
    {ℓ₀ ℓ₁ ℓ₂ : ℤ} (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) :
    r.x ^ (4 : ℤ) = r.c ^ (4 * ℓ₀ - ℓ₂) := by
  have h : r.x ^ (4 : ℤ) * r.y ^ (4 : ℤ) = r.c ^ (4 * ℓ₀) := by
    calc
      r.x ^ (4 : ℤ) * r.y ^ (4 : ℤ) = (r.x * r.y) ^ (4 : ℤ) :=
        (r.commute_xy.mul_zpow 4).symm
      _ = (r.c ^ ℓ₀) ^ (4 : ℤ) := by rw [r.xy]
      _ = r.c ^ (ℓ₀ * 4) := (zpow_mul r.c ℓ₀ 4).symm
      _ = r.c ^ (4 * ℓ₀) := by rw [mul_comm ℓ₀ 4]
  rw [r.y_fourth] at h
  calc
    r.x ^ (4 : ℤ) = (r.x ^ (4 : ℤ) * r.c ^ ℓ₂) * (r.c ^ ℓ₂)⁻¹ := by simp
    _ = r.c ^ (4 * ℓ₀) * (r.c ^ ℓ₂)⁻¹ := by rw [h]
    _ = r.c ^ (4 * ℓ₀ - ℓ₂) := by rw [zpow_sub]

/-- Evaluation of the exponent pair `(a,b)` as `x^a c^b` in any group carrying the paper's
relations. -/
public def paperEvaluation {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) : (Fin 2 → ℤ) →+ Additive G where
  toFun z := Additive.ofMul (r.x ^ z 0 * r.c ^ z 1)
  map_zero' := by simp
  map_add' a b := by
    change r.x ^ (a 0 + b 0) * r.c ^ (a 1 + b 1) =
      (r.x ^ a 0 * r.c ^ a 1) * (r.x ^ b 0 * r.c ^ b 1)
    rw [zpow_add, zpow_add]
    exact ((r.central_c r.x).symm.zpow_zpow (b 0) (a 1)).mul_mul_mul_comm
      (r.x ^ a 0) (r.c ^ b 1)

@[simp]
public theorem paperEvaluation_first_relation {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) :
    paperEvaluation r ![3, -ℓ₁] = 0 := by
  change Additive.ofMul (r.x ^ (3 : ℤ) * r.c ^ (-ℓ₁)) = 0
  rw [r.x_cube, zpow_neg]
  simp

@[simp]
public theorem paperEvaluation_second_relation {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) :
    paperEvaluation r ![4, ℓ₂ - 4 * ℓ₀] = 0 := by
  change Additive.ofMul (r.x ^ (4 : ℤ) * r.c ^ (ℓ₂ - 4 * ℓ₀)) = 0
  rw [r.x_fourth, ← zpow_add]
  simp

/-- Every row combination in the displayed presentation evaluates to the identity. -/
public theorem paperEvaluation_relation {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) (a : Fin 2 → ℤ) :
    paperEvaluation r (paperRelationMap ℓ₀ ℓ₁ ℓ₂ a) = 0 := by
  have hv : paperRelationMap ℓ₀ ℓ₁ ℓ₂ a =
      a 0 • ![3, -ℓ₁] + a 1 • ![4, ℓ₂ - 4 * ℓ₀] := by
    funext i
    fin_cases i <;> simp [paperRelationMap] <;> ring
  rw [hv, map_add, map_zsmul, map_zsmul, paperEvaluation_first_relation r,
    paperEvaluation_second_relation r]
  simp

public theorem paperClassifier_ker_le_evaluation_ker {G : Type*} [Group G]
    {ℓ₀ ℓ₁ ℓ₂ : ℤ} (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) :
    (paperCyclicClassifier ℓ₀ ℓ₁ ℓ₂).ker ≤ (paperEvaluation r).ker := by
  intro z hz
  have hz' : z ∈ (paperRelationMap ℓ₀ ℓ₁ ℓ₂).range := by
    rw [paperRelation_range_eq_kernel]
    exact hz
  obtain ⟨a, rfl⟩ := hz'
  exact paperEvaluation_relation r a

/-- The canonical additive map out of the quotient presentation. -/
public def paperCanonicalAddHom {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) :
    PaperAdditivePresentation ℓ₀ ℓ₁ ℓ₂ →+ Additive G :=
  QuotientAddGroup.lift _ (paperEvaluation r) (paperClassifier_ker_le_evaluation_ker r)

/-- The universal homomorphism from the presented group into any group satisfying its relations. -/
public def paperCanonicalHom {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) :
    PaperPresentedGroup ℓ₀ ℓ₁ ℓ₂ →* G :=
  AddMonoidHom.toMultiplicative (paperCanonicalAddHom r)

@[simp]
public theorem paperCanonicalAddHom_c {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) :
    paperCanonicalAddHom r (paperCAdd ℓ₀ ℓ₁ ℓ₂) = Additive.ofMul r.c := by
  rw [show paperCanonicalAddHom r (paperCAdd ℓ₀ ℓ₁ ℓ₂) = paperEvaluation r ![0, 1] by
    exact QuotientAddGroup.lift_mk _ _ _]
  simp [paperEvaluation]

@[simp]
public theorem paperCanonicalAddHom_x {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) :
    paperCanonicalAddHom r (paperXAdd ℓ₀ ℓ₁ ℓ₂) = Additive.ofMul r.x := by
  rw [show paperCanonicalAddHom r (paperXAdd ℓ₀ ℓ₁ ℓ₂) = paperEvaluation r ![1, 0] by
    exact QuotientAddGroup.lift_mk _ _ _]
  simp [paperEvaluation]

@[simp]
public theorem paperCanonicalHom_c {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) :
    paperCanonicalHom r (Multiplicative.ofAdd (paperCAdd ℓ₀ ℓ₁ ℓ₂)) = r.c := by
  exact congrArg Additive.toMul (paperCanonicalAddHom_c r)

@[simp]
public theorem paperCanonicalHom_x {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) :
    paperCanonicalHom r (Multiplicative.ofAdd (paperXAdd ℓ₀ ℓ₁ ℓ₂)) = r.x := by
  exact congrArg Additive.toMul (paperCanonicalAddHom_x r)

@[simp]
public theorem paperCanonicalHom_y {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) :
    paperCanonicalHom r (Multiplicative.ofAdd (paperYAdd ℓ₀ ℓ₁ ℓ₂)) = r.y := by
  change Additive.toMul (paperCanonicalAddHom r (paperYAdd ℓ₀ ℓ₁ ℓ₂)) = r.y
  rw [paperYAdd, map_sub, map_zsmul, paperCanonicalAddHom_c, paperCanonicalAddHom_x,
    toMul_sub, toMul_zsmul]
  simp only [toMul_ofMul, div_eq_mul_inv]
  rw [← r.xy, r.commute_xy.eq]
  simp

/-- The displayed generators generate the target group. -/
public def PaperGeneratorsGenerate {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) : Prop :=
  Subgroup.closure {r.c, r.x, r.y} = ⊤

/-- Generation of the target by `c,x,y` makes the canonical homomorphism surjective. -/
public theorem paperCanonicalHom_surjective {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) (hg : PaperGeneratorsGenerate r) :
    Function.Surjective (paperCanonicalHom r) := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← hg]
  apply (Subgroup.closure_le _).2
  intro g hg'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg'
  rcases hg' with rfl | rfl | rfl
  · exact ⟨Multiplicative.ofAdd (paperCAdd ℓ₀ ℓ₁ ℓ₂), paperCanonicalHom_c r⟩
  · exact ⟨Multiplicative.ofAdd (paperXAdd ℓ₀ ℓ₁ ℓ₂), paperCanonicalHom_x r⟩
  · exact ⟨Multiplicative.ofAdd (paperYAdd ℓ₀ ℓ₁ ℓ₂), paperCanonicalHom_y r⟩

/-- No additional relation among the normal-form words `x^a c^b` holds in the target. -/
public def HasNoExtraPaperRelations {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) : Prop :=
  ∀ z : Fin 2 → ℤ, r.x ^ z 0 * r.c ^ z 1 = 1 →
    paperCyclicClassifier ℓ₀ ℓ₁ ℓ₂ z = 0

/-- The no-extra-relations normal form makes the canonical map injective. -/
public theorem paperCanonicalAddHom_injective {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) (hn : HasNoExtraPaperRelations r) :
    Function.Injective (paperCanonicalAddHom r) := by
  rw [← AddMonoidHom.ker_eq_bot_iff]
  ext q
  constructor
  · intro hq
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    change (QuotientAddGroup.mk z : PaperAdditivePresentation ℓ₀ ℓ₁ ℓ₂) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_ker]
    apply hn z
    change Additive.toMul (paperEvaluation r z) = 1
    apply congrArg Additive.toMul at hq
    simpa [paperCanonicalAddHom, QuotientAddGroup.lift_mk] using hq
  · intro hq
    change paperCanonicalAddHom r q = 0
    have hq' : q = 0 := by simpa using hq
    rw [hq']
    simp

public theorem paperCanonicalHom_injective {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) (hn : HasNoExtraPaperRelations r) :
    Function.Injective (paperCanonicalHom r) := by
  intro a b hab
  exact paperCanonicalAddHom_injective r hn hab

/-- The universal map is an equivalence exactly once generation and the absence of extra
relations have been verified. -/
public noncomputable def paperCanonicalEquiv {G : Type*} [Group G] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (r : SatisfiesPaperRelations G ℓ₀ ℓ₁ ℓ₂) (hg : PaperGeneratorsGenerate r)
    (hn : HasNoExtraPaperRelations r) : PaperPresentedGroup ℓ₀ ℓ₁ ℓ₂ ≃* G :=
  MulEquiv.ofBijective (paperCanonicalHom r)
    ⟨paperCanonicalHom_injective r hn, paperCanonicalHom_surjective r hg⟩

/-- Concrete van Kampen data: generators satisfying the displayed relations, generation, and the
normal-form assertion that there are no further relations. -/
public def HasVanKampenData (X : Type*) [TopologicalSpace X] (ℓ₀ ℓ₁ ℓ₂ : ℤ) : Prop :=
  ∃ x₀ : X, ∃ r : SatisfiesPaperRelations (FundamentalGroup X x₀) ℓ₀ ℓ₁ ℓ₂,
    PaperGeneratorsGenerate r ∧ HasNoExtraPaperRelations r

/-- The compressed form of the van Kampen input: an equivalence with the verified presentation. -/
public def HasVanKampenPresentation (X : Type*) [TopologicalSpace X] (ℓ₀ ℓ₁ ℓ₂ : ℤ) : Prop :=
  ∃ x₀ : X, Nonempty (FundamentalGroup X x₀ ≃* PaperPresentedGroup ℓ₀ ℓ₁ ℓ₂)

/-- Concrete generators, relations, generation, and no-extra-relations imply the compressed
presentation contract. -/
public theorem HasVanKampenData.hasVanKampenPresentation
    {X : Type*} [TopologicalSpace X] {ℓ₀ ℓ₁ ℓ₂ : ℤ}
    (h : HasVanKampenData X ℓ₀ ℓ₁ ℓ₂) : HasVanKampenPresentation X ℓ₀ ℓ₁ ℓ₂ := by
  obtain ⟨x₀, r, hg, hn⟩ := h
  exact ⟨x₀, ⟨(paperCanonicalEquiv r hg hn).symm⟩⟩

@[simp]
public theorem chosen_paperObstruction : paperObstruction 0 1 (-1) = -1 := by
  norm_num [paperObstruction]

/-- The chosen presentation is the trivial group. -/
public theorem chosenPaperPresentedGroup_subsingleton :
    Subsingleton (PaperPresentedGroup 0 1 (-1)) := by
  constructor
  intro a b
  apply (paperPresentedGroupEquiv 0 1 (-1)).injective
  have h : Subsingleton (Multiplicative (ZMod 1)) := inferInstance
  exact @Subsingleton.elim _ (by simpa [paperObstruction] using h) _ _

/-- For the chosen twists, the cyclic target is definitionally the obstruction group already used by
`HasPaperFundamentalGroup`. -/
public noncomputable def chosenPaperPresentedGroupEquivObstruction :
    PaperPresentedGroup 0 1 (-1) ≃* Multiplicative TwistObstruction.ObstructionGroup := by
  let hmod : (paperObstruction 0 1 (-1)).natAbs = TwistObstruction.p.natAbs := by
    calc
      (paperObstruction 0 1 (-1)).natAbs = 1 := by norm_num [paperObstruction]
      _ = TwistObstruction.p.natAbs := TwistObstruction.natAbs_p.symm
  exact (paperPresentedGroupEquiv 0 1 (-1)).trans
    (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hmod).toAddEquiv)

/-- The verified presentation calculation supplies the existing paper fundamental-group contract. -/
public theorem HasVanKampenPresentation.hasPaperFundamentalGroup
    {X : Type*} [TopologicalSpace X] (h : HasVanKampenPresentation X 0 1 (-1)) :
    HasPaperFundamentalGroup X := by
  obtain ⟨x₀, ⟨e⟩⟩ := h
  exact ⟨x₀, ⟨e.trans chosenPaperPresentedGroupEquivObstruction⟩⟩

end SphereSixComplex.Topology
