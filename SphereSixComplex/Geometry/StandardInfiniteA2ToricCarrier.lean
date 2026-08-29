/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Geometry.A2ConeUnimodularity
public import SphereSixComplex.Geometry.AtlasTransport
public import SphereSixComplex.Geometry.GluingCompatibility

/-!
# The glued carrier of the standard infinite `A₂` toric model

This module constructs the topological gluing of the affine charts of the infinite height-one
`A₂` fan.  It also supplies its countable complex-manifold atlas.  The construction is a focused
adaptation of the toric gluing in Boris Alexeev's Apache-2.0 `HopfProblem/Solution.lean`, expressed
here using this project's existing fan combinatorics and `ComplexModel`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Function Matrix Set Topology
open scoped ContDiff Manifold
open SphereSixComplex.Geometry.CuspCombinatorics

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- The two affine triangles based at each lattice point. -/
public abbrev ChartIndex := Bool × ToricLattice

/-- Raw affine coordinates, used internally before recharting to `ComplexModel`. -/
public abbrev RawCoordinates := Fin 3 → ℂ

/-- The matrix whose rows are the dual characters of a maximal cone. -/
public def dualMatrix (a : ChartIndex) : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j ↦ a2DualCharacter a.1 a.2 i j

public theorem dualMatrix_mul_coneMatrix (a : ChartIndex) :
    dualMatrix a * a2ConeMatrix a.1 a.2 = 1 := by
  rcases a with ⟨upper, v⟩
  ext i j
  cases upper <;> fin_cases i <;> fin_cases j <;>
    simp [dualMatrix, a2DualCharacter, a2ConeMatrix, heightOneRay,
      CuspFilling.a2Triangle, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

public theorem coneMatrix_mul_dualMatrix (a : ChartIndex) :
    a2ConeMatrix a.1 a.2 * dualMatrix a = 1 := by
  rcases a with ⟨upper, v⟩
  ext i j
  cases upper <;> fin_cases i <;> fin_cases j <;>
    simp [dualMatrix, a2DualCharacter, a2ConeMatrix, heightOneRay,
      CuspFilling.a2Triangle, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

@[simp]
public theorem coneMatrix_last (a : ChartIndex) (j : Fin 3) :
    a2ConeMatrix a.1 a.2 2 j = 1 :=
  heightOneRay_last _

/-- A Laurent monomial map in affine coordinates. -/
public def monomial (A : Matrix (Fin 3) (Fin 3) ℤ) (z : RawCoordinates) : RawCoordinates :=
  fun i ↦ ∏ j, z j ^ A i j

/-- The largest coordinate open set on which a Laurent monomial is defined. -/
public def monomialDomain (A : Matrix (Fin 3) (Fin 3) ℤ) : Set RawCoordinates :=
  {z | ∀ i j, A i j < 0 → z j ≠ 0}

public theorem monomialDomain_isOpen (A : Matrix (Fin 3) (Fin 3) ℤ) :
    IsOpen (monomialDomain A) := by
  unfold monomialDomain
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases h : A i j < 0
  · simpa [h] using isOpen_ne_fun (continuous_apply j) continuous_const
  · simp [h]

/-- The dense coordinate torus. -/
public def coordinateTorus : Set RawCoordinates := {z | ∀ j, z j ≠ 0}

public theorem coordinateTorus_isDense : Dense coordinateTorus := by
  simpa [coordinateTorus, Set.pi] using
    (dense_pi (Set.univ : Set (Fin 3)) fun _ _ ↦ dense_compl_singleton (0 : ℂ))

public theorem coordinateTorus_subset_monomialDomain
    (A : Matrix (Fin 3) (Fin 3) ℤ) : coordinateTorus ⊆ monomialDomain A :=
  fun _ hz _ j _ ↦ hz j

public theorem monomial_mapsTo_coordinateTorus (A : Matrix (Fin 3) (Fin 3) ℤ) :
    MapsTo (monomial A) coordinateTorus coordinateTorus := by
  intro z hz i
  exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ zpow_ne_zero _ (hz j)

public theorem monomial_contDiffOn (A : Matrix (Fin 3) (Fin 3) ℤ) (n : ℕ∞ω) :
    ContDiffOn ℂ n (monomial A) (monomialDomain A) := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_prod
  intro j _
  cases h : A i j with
  | ofNat k =>
      simpa only [h, Int.ofNat_eq_natCast, zpow_natCast] using
        (contDiff_apply ℂ ℂ j).contDiffOn.pow k
  | negSucc k =>
      have hn : A i j < 0 := by omega
      intro z hz
      simpa only [h, zpow_negSucc] using
        ((contDiff_apply ℂ ℂ j).contDiffWithinAt.pow (k + 1)).fun_inv
          (pow_ne_zero _ (hz i j hn))

private theorem prod_zpow_eq {a : ℂ} (ha : a ≠ 0)
    (s : Finset (Fin 3)) (k : Fin 3 → ℤ) :
    (∏ i ∈ s, a ^ k i) = a ^ ∑ i ∈ s, k i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add₀ ha]

public theorem monomial_comp_on_coordinateTorus
    (A B : Matrix (Fin 3) (Fin 3) ℤ) {z : RawCoordinates}
    (hz : z ∈ coordinateTorus) : monomial A (monomial B z) = monomial (A * B) z := by
  funext i
  simp only [monomial, Matrix.mul_apply]
  calc
    (∏ k, (∏ j, z j ^ B k j) ^ A i k) =
        ∏ k, ∏ j, z j ^ (A i k * B k j) := by
      apply Finset.prod_congr rfl
      intro k _
      rw [← Finset.prod_zpow]
      apply Finset.prod_congr rfl
      intro j _
      rw [← zpow_mul, mul_comm]
    _ = ∏ j, ∏ k, z j ^ (A i k * B k j) := Finset.prod_comm
    _ = ∏ j, z j ^ ∑ k, A i k * B k j := by
      apply Finset.prod_congr rfl
      intro j _
      exact prod_zpow_eq (hz j) _ _

@[simp]
public theorem monomial_one (z : RawCoordinates) : monomial 1 z = z := by
  funext i
  simp [monomial, Matrix.one_apply]

public theorem monomial_mul (A : Matrix (Fin 3) (Fin 3) ℤ)
    (z w : RawCoordinates) : monomial A (z * w) = monomial A z * monomial A w := by
  funext i
  simp [monomial, mul_zpow, Finset.prod_mul_distrib]

/-- Every column has total height one. -/
public def HeightOne (A : Matrix (Fin 3) (Fin 3) ℤ) : Prop :=
  ∀ j, ∑ i, A i j = 1

private theorem column_single_of_zero {A : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : HeightOne A) {z : RawCoordinates} (hz : z ∈ monomialDomain A)
    {j : Fin 3} (hj : z j = 0) :
    ∃ k : Fin 3, ∀ i, A i j = if i = k then 1 else 0 := by
  have hn (i : Fin 3) : 0 ≤ A i j := by
    by_contra h
    exact hz i j (lt_of_not_ge h) hj
  have hsum := hA j
  simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Fin.sum_univ_zero, add_zero] at hsum
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have hcases : A 0 j = 1 ∨ A 1 j = 1 ∨ A 2 j = 1 := by omega
  rcases hcases with h | h | h
  · refine ⟨0, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega
  · refine ⟨1, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega
  · refine ⟨2, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega

private theorem monomial_zero_of_column_single {A : Matrix (Fin 3) (Fin 3) ℤ}
    {z : RawCoordinates} {j k : Fin 3} (hj : z j = 0)
    (hc : ∀ i, A i j = if i = k then 1 else 0) : monomial A z k = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hj, hc]

private theorem inverse_mapsTo_domain {A B : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : HeightOne A) (hBA : B * A = 1) :
    MapsTo (monomial A) (monomialDomain A) (monomialDomain B) := by
  intro z hz i k hB hzero
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hzero
  have hzj : z j = 0 := eq_zero_of_zpow_eq_zero hj
  have hAj : A k j ≠ 0 := by
    intro he
    simp [he] at hj
  obtain ⟨l, hl⟩ := column_single_of_zero hA hz hzj
  have hkl : k = l := by
    by_contra h
    exact hAj (by simp [hl, h])
  subst l
  have hentry := congrFun (congrFun hBA i) j
  have hnonneg : 0 ≤ B i k := by
    have he : B i k = (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := by
      simpa [Matrix.mul_apply, hl] using hentry
    rw [he, Matrix.one_apply]
    split_ifs <;> norm_num
  exact (not_lt_of_ge hnonneg) hB

/-- Domain on which two inverse Laurent monomials define a coordinate change. -/
public def overlap (A B : Matrix (Fin 3) (Fin 3) ℤ) : Set RawCoordinates :=
  monomialDomain A ∩ monomial A ⁻¹' monomialDomain B

public theorem overlap_isOpen (A B : Matrix (Fin 3) (Fin 3) ℤ) : IsOpen (overlap A B) :=
  (monomial_contDiffOn A 0).continuousOn.isOpen_inter_preimage
    (monomialDomain_isOpen A) (monomialDomain_isOpen B)

public theorem coordinateTorus_subset_overlap (A B : Matrix (Fin 3) (Fin 3) ℤ) :
    coordinateTorus ⊆ overlap A B := fun _ hz ↦
  ⟨coordinateTorus_subset_monomialDomain A hz,
    coordinateTorus_subset_monomialDomain B (monomial_mapsTo_coordinateTorus A hz)⟩

public theorem overlap_eq_monomialDomain {A B : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : HeightOne A) (hBA : B * A = 1) :
    overlap A B = monomialDomain A :=
  Set.inter_eq_left.mpr (inverse_mapsTo_domain hA hBA)

private theorem overlap_subset_composite_domain {A B : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : HeightOne A) : overlap A B ⊆ monomialDomain (B * A) := by
  intro z hz i j hC hzj
  obtain ⟨k, hk⟩ := column_single_of_zero hA hz.1 hzj
  have hzAk : monomial A z k = 0 := monomial_zero_of_column_single hzj hk
  have hBk : B i k < 0 := by simpa [Matrix.mul_apply, hk] using hC
  exact hz.2 i k hBk hzAk

private theorem monomial_comp_on_overlap {A B : Matrix (Fin 3) (Fin 3) ℤ}
    (hA : HeightOne A) :
    EqOn (monomial B ∘ monomial A) (monomial (B * A)) (overlap A B) := by
  have h : EqOn (monomial B ∘ monomial A) (monomial (B * A))
      (overlap A B ∩ coordinateTorus) :=
    fun _ hz ↦ monomial_comp_on_coordinateTorus B A hz.2
  refine h.of_subset_closure ?_ ?_ Set.inter_subset_left
    (coordinateTorus_isDense.open_subset_closure_inter (overlap_isOpen A B))
  · exact (monomial_contDiffOn B 0).continuousOn.comp
      ((monomial_contDiffOn A 0).continuousOn.mono Set.inter_subset_left)
      (fun _ hz ↦ hz.2)
  · exact (monomial_contDiffOn (B * A) 0).continuousOn.mono
      (overlap_subset_composite_domain hA)

public theorem monomial_inverse_on_overlap (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (hBA : B * A = 1) : EqOn (monomial B ∘ monomial A) id (overlap A B) := by
  have h : EqOn (monomial B ∘ monomial A) id (overlap A B ∩ coordinateTorus) := by
    intro z hz
    simpa [hBA] using monomial_comp_on_coordinateTorus B A hz.2
  refine h.of_subset_closure ?_ continuousOn_id Set.inter_subset_left
    (coordinateTorus_isDense.open_subset_closure_inter (overlap_isOpen A B))
  exact (monomial_contDiffOn B 0).continuousOn.comp
    ((monomial_contDiffOn A 0).continuousOn.mono Set.inter_subset_left)
    (fun _ hz ↦ hz.2)

/-- The partial homeomorphism associated to a pair of mutually inverse Laurent monomials. -/
public def monomialChange (A B : Matrix (Fin 3) (Fin 3) ℤ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    OpenPartialHomeomorph RawCoordinates RawCoordinates where
  toFun := monomial A
  invFun := monomial B
  source := overlap A B
  target := overlap B A
  map_source' z hz :=
    ⟨hz.2, by
      change (monomial B ∘ monomial A) z ∈ monomialDomain A
      rw [monomial_inverse_on_overlap A B hBA hz]
      exact hz.1⟩
  map_target' z hz :=
    ⟨hz.2, by
      change (monomial A ∘ monomial B) z ∈ monomialDomain B
      rw [monomial_inverse_on_overlap B A hAB hz]
      exact hz.1⟩
  left_inv' := monomial_inverse_on_overlap A B hBA
  right_inv' := monomial_inverse_on_overlap B A hAB
  open_source := overlap_isOpen A B
  open_target := overlap_isOpen B A
  continuousOn_toFun := (monomial_contDiffOn A 0).continuousOn.mono Set.inter_subset_left
  continuousOn_invFun := (monomial_contDiffOn B 0).continuousOn.mono Set.inter_subset_left

/-- The integral transition matrix from chart `a` to chart `b`. -/
public def transitionMatrix (a b : ChartIndex) : Matrix (Fin 3) (Fin 3) ℤ :=
  dualMatrix b * a2ConeMatrix a.1 a.2

@[simp]
public theorem transitionMatrix_self (a : ChartIndex) : transitionMatrix a a = 1 :=
  dualMatrix_mul_coneMatrix a

public theorem transitionMatrix_mul (a b c : ChartIndex) :
    transitionMatrix b c * transitionMatrix a b = transitionMatrix a c := by
  unfold transitionMatrix
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (a2ConeMatrix b.1 b.2),
    coneMatrix_mul_dualMatrix, Matrix.one_mul]

private theorem coneMatrix_mul_transitionMatrix (a b : ChartIndex) :
    a2ConeMatrix b.1 b.2 * transitionMatrix a b = a2ConeMatrix a.1 a.2 := by
  rw [transitionMatrix, ← Matrix.mul_assoc, coneMatrix_mul_dualMatrix, Matrix.one_mul]

public theorem transitionMatrix_heightOne (a b : ChartIndex) :
    HeightOne (transitionMatrix a b) := by
  intro j
  have h := congrFun (congrFun (coneMatrix_mul_transitionMatrix a b) 2) j
  simpa [a2ConeMatrix, heightOneRay, Matrix.mul_apply] using h

/-- The affine-coordinate transition between two maximal cones. -/
public def chartChange (a b : ChartIndex) :
    OpenPartialHomeomorph RawCoordinates RawCoordinates :=
  monomialChange (transitionMatrix a b) (transitionMatrix b a)
    (by rw [transitionMatrix_mul, transitionMatrix_self])
    (by rw [transitionMatrix_mul, transitionMatrix_self])

@[simp]
public theorem chartChange_source (a b : ChartIndex) :
    (chartChange a b).source = monomialDomain (transitionMatrix a b) :=
  overlap_eq_monomialDomain (transitionMatrix_heightOne a b)
    (by rw [transitionMatrix_mul, transitionMatrix_self])

@[simp]
public theorem chartChange_self_source (a : ChartIndex) :
    (chartChange a a).source = Set.univ := by
  rw [chartChange_source, transitionMatrix_self]
  ext z
  simp only [monomialDomain, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro i j h
  simp only [Matrix.one_apply] at h
  split_ifs at h <;> omega

@[simp]
public theorem chartChange_self_apply (a : ChartIndex) (z : RawCoordinates) :
    chartChange a a z = z := by
  change monomial (transitionMatrix a a) z = z
  rw [transitionMatrix_self, monomial_one]

public theorem chartChange_cocycle (a b c : ChartIndex) {z : RawCoordinates}
    (hz : z ∈ (chartChange a b).source)
    (hbz : chartChange a b z ∈ (chartChange b c).source) :
    z ∈ (chartChange a c).source ∧
      chartChange b c (chartChange a b z) = chartChange a c z := by
  rw [chartChange_source] at hz hbz ⊢
  have hm : z ∈ overlap (transitionMatrix a b) (transitionMatrix b c) := ⟨hz, hbz⟩
  constructor
  · simpa only [transitionMatrix_mul] using
      overlap_subset_composite_domain (transitionMatrix_heightOne a b) hm
  · change monomial (transitionMatrix b c) (monomial (transitionMatrix a b) z) =
      monomial (transitionMatrix a c) z
    simpa only [Function.comp_apply, transitionMatrix_mul] using
      monomial_comp_on_overlap (transitionMatrix_heightOne a b) hm

public theorem chartChange_inter (a b c : ChartIndex) {z : RawCoordinates}
    (hb : z ∈ (chartChange a b).source) (hc : z ∈ (chartChange a c).source) :
    chartChange a b z ∈ (chartChange b c).source := by
  have hi : chartChange a b z ∈ (chartChange b a).source := (chartChange a b).map_source hb
  have hinv : chartChange b a (chartChange a b z) = z := (chartChange a b).left_inv hb
  exact (chartChange_cocycle b a c hi (by rwa [hinv])).1

public theorem chartChange_contDiffOn (a b : ChartIndex) :
    ContDiffOn ℂ ω (chartChange a b) (chartChange a b).source :=
  (monomial_contDiffOn (transitionMatrix a b) ω).mono Set.inter_subset_left

/-- The topological gluing datum of all affine charts of the infinite fan. -/
public abbrev gluingCore : TopCat.GlueData.MkCore where
  J := ChartIndex
  U := fun _ ↦ TopCat.of RawCoordinates
  V a b := ⟨(chartChange a b).source, (chartChange a b).open_source⟩
  t a b := TopCat.ofHom
    { toFun := fun z ↦ ⟨chartChange a b z, (chartChange a b).map_source z.2⟩
      continuous_toFun := (chartChange a b).continuousOn.domRestrict.subtype_mk _ }
  V_id a := by
    apply TopologicalSpace.Opens.ext
    exact chartChange_self_source a
  t_id a := by
    funext z
    exact Subtype.ext (chartChange_self_apply a z.1)
  t_inter := by
    intro a b c z hz
    exact chartChange_inter a b c z.2 hz
  cocycle a b c z hz :=
    (chartChange_cocycle a b c z.2 (chartChange_inter a b c z.2 hz)).2

/-- The assembled gluing data. -/
public abbrev gluing : TopCat.GlueData := TopCat.GlueData.mk' gluingCore

/-- The carrier obtained by gluing all affine `A₂` toric charts. -/
public abbrev Carrier := GluedSpace gluing

/-- Inclusion of an affine chart into the glued carrier. -/
public def inclusion (a : ChartIndex) : RawCoordinates → Carrier :=
  gluing.toGlueData.ι a

public theorem inclusion_isOpenEmbedding (a : ChartIndex) : IsOpenEmbedding (inclusion a) :=
  gluing.ι_isOpenEmbedding a

public theorem inclusion_jointly_surjective (x : Carrier) :
    ∃ a z, inclusion a z = x :=
  gluing.ι_jointly_surjective x

public theorem inclusion_eq_iff (a b : ChartIndex) (z w : RawCoordinates) :
    inclusion a z = inclusion b w ↔
      z ∈ (chartChange a b).source ∧ chartChange a b z = w := by
  refine (gluing.ι_eq_iff_rel a b z w).trans ?_
  constructor
  · rintro ⟨⟨q, hq⟩, h1, h2⟩
    change q = z at h1
    change chartChange a b q = w at h2
    subst q
    exact ⟨hq, h2⟩
  · rintro ⟨hz, he⟩
    exact ⟨⟨z, hz⟩, rfl, he⟩

/-- The parametrization of the glued carrier by one affine chart. -/
public def parametrization (a : ChartIndex) :
    OpenPartialHomeomorph RawCoordinates Carrier :=
  (inclusion_isOpenEmbedding a).toOpenPartialHomeomorph (inclusion a)

@[simp]
public theorem parametrization_target (a : ChartIndex) :
    (parametrization a).target = Set.range (inclusion a) := by
  simp [parametrization]

private theorem parametrization_transition (a b : ChartIndex) {z : RawCoordinates}
    (hz : inclusion a z ∈ Set.range (inclusion b)) :
    z ∈ (chartChange a b).source ∧
      (parametrization b).symm (inclusion a z) = chartChange a b z := by
  obtain ⟨w, hw⟩ := hz
  have he := (inclusion_eq_iff a b z w).mp hw.symm
  refine ⟨he.1, ?_⟩
  rw [← hw]
  exact ((inclusion_isOpenEmbedding b).toOpenPartialHomeomorph_left_inv).trans he.2.symm

public noncomputable def preferredChart (x : Carrier) : ChartIndex :=
  (inclusion_jointly_surjective x).choose

public theorem preferredChart_mem (x : Carrier) :
    x ∈ Set.range (inclusion (preferredChart x)) :=
  (inclusion_jointly_surjective x).choose_spec

/-- The raw affine atlas before its model is recharted to `ComplexModel`. -/
@[instance_reducible]
public noncomputable def rawChartedSpace : ChartedSpace RawCoordinates Carrier where
  atlas := Set.range (fun a : ChartIndex ↦ (parametrization a).symm)
  chartAt x := (parametrization (preferredChart x)).symm
  mem_chart_source x := by
    change x ∈ (parametrization (preferredChart x)).target
    rw [parametrization_target]
    exact preferredChart_mem x
  chart_mem_atlas x := Set.mem_range_self _

/-- The raw atlas is a complex manifold atlas because all transitions are Laurent monomials. -/
public theorem rawIsManifold :
    letI := rawChartedSpace
    IsManifold (modelWithCornersSelf ℂ RawCoordinates) ∞ Carrier := by
  let _ := rawChartedSpace
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨a, rfl⟩ := he
  obtain ⟨b, rfl⟩ := he'
  have hparam (a : ChartIndex) (z : RawCoordinates) : parametrization a z = inclusion a z := rfl
  have h :
      ∀ z ∈ ((parametrization a).trans (parametrization b).symm).source,
        z ∈ (chartChange a b).source ∧
          ((parametrization a).trans (parametrization b).symm) z = chartChange a b z := by
    intro z hz
    exact parametrization_transition a b (by simpa [hparam] using hz.2)
  simpa using ((((chartChange_contDiffOn a b).mono (fun z hz ↦ (h z hz).1)).congr
    (fun z hz ↦ (h z hz).2)).of_le (by simp : (∞ : ℕ∞ω) ≤ ω))

/-- The raw coordinate model and the project's `ComplexModel` are linearly equivalent. -/
public noncomputable def rawToComplexModel : RawCoordinates ≃L[ℂ] ComplexModel :=
  (EuclideanSpace.equiv (Fin 3) ℂ).symm

/-- The canonical `ComplexModel` atlas on the glued carrier. -/
@[instance_reducible]
public noncomputable def chartedSpace : ChartedSpace ComplexModel Carrier := by
  let _ : ChartedSpace RawCoordinates Carrier := rawChartedSpace
  exact linearRechart rawToComplexModel

/-- The glued carrier is a complex three-manifold. -/
public theorem isManifold :
    letI := chartedSpace
    IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ Carrier := by
  let _ : ChartedSpace RawCoordinates Carrier := rawChartedSpace
  let _ : IsManifold (modelWithCornersSelf ℂ RawCoordinates) ∞ Carrier := rawIsManifold
  exact isManifold_linearRechart rawToComplexModel

/-- Countability of the fan gives the glued carrier a second-countable topology. -/
public instance chartIndexCountable : Countable ChartIndex := by
  apply Function.Injective.countable
    (f := fun a : ChartIndex ↦ (a.1, a.2 0, a.2 1))
  rintro ⟨u, v⟩ ⟨u', v'⟩ h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨rfl, h0, h1⟩
  congr 1
  funext i
  fin_cases i
  · exact h0
  · exact h1

public theorem secondCountableTopology : SecondCountableTopology Carrier := by
  let _ : Countable gluing.J := chartIndexCountable
  let _ (i : gluing.J) : SecondCountableTopology (gluing.U i) := by
    change SecondCountableTopology RawCoordinates
    infer_instance
  exact secondCountableTopology_gluedSpace gluing

private def stripIndex (a : ChartIndex) : Fin 3 → ℤ :=
  ![a.2 0, a.2 1, a.2 0 + a.2 1 + if a.1 then 1 else 0]

private def pencil (k : Fin 3) (x : Fin 3 → ℤ) : ℤ :=
  ![x 0, x 1, x 0 + x 1] k

private def separationSign (a b : ℤ) : ℤ :=
  if a < b then -1 else if b < a then 1 else 0

private def stripValue (a b x : ℤ) : ℤ :=
  separationSign a b * (2 * x - a - b - 1)

private theorem separationSign_swap (a b : ℤ) : separationSign b a = -separationSign a b := by
  unfold separationSign
  split_ifs <;> omega

private theorem stripValue_nonneg {a b x : ℤ} (hx : a ≤ x ∧ x ≤ a + 1) :
    0 ≤ stripValue a b x := by
  unfold stripValue separationSign
  split_ifs <;> omega

private theorem stripValue_zero_bounds {a b x : ℤ} (hx : a ≤ x ∧ x ≤ a + 1)
    (hzero : stripValue a b x = 0) : b ≤ x ∧ x ≤ b + 1 := by
  unfold stripValue separationSign at hzero
  split_ifs at hzero <;> omega

private theorem ray_strip_bounds (a : ChartIndex) (j k : Fin 3) :
    stripIndex a k ≤ pencil k (fun i ↦ a2ConeMatrix a.1 a.2 i j) ∧
      pencil k (fun i ↦ a2ConeMatrix a.1 a.2 i j) ≤ stripIndex a k + 1 := by
  rcases a with ⟨upper, v⟩
  cases upper <;> fin_cases j <;> fin_cases k <;>
    simp [stripIndex, pencil, a2ConeMatrix, heightOneRay, CuspFilling.a2Triangle] <;> omega

private theorem transition_nonneg_of_bounds (a b : ChartIndex) (j : Fin 3)
    (h : ∀ k, stripIndex b k ≤ pencil k (fun i ↦ a2ConeMatrix a.1 a.2 i j) ∧
      pencil k (fun i ↦ a2ConeMatrix a.1 a.2 i j) ≤ stripIndex b k + 1) :
    ∀ i, 0 ≤ transitionMatrix a b i j := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rcases b with ⟨upper, v⟩
  intro i
  cases upper <;> fin_cases i <;>
    simp [transitionMatrix, dualMatrix, a2DualCharacter, Matrix.mul_apply,
      Fin.sum_univ_succ, coneMatrix_last] <;>
    simp [stripIndex, pencil] at h0 h1 h2 <;> omega

private def separationCharacter (a b : ChartIndex) : Fin 3 → ℤ :=
  let e : Fin 3 → ℤ := fun k ↦ separationSign (stripIndex a k) (stripIndex b k)
  ![2 * (e 0 + e 2), 2 * (e 1 + e 2),
    -(e 0 * (stripIndex a 0 + stripIndex b 0 + 1) +
      e 1 * (stripIndex a 1 + stripIndex b 1 + 1) +
      e 2 * (stripIndex a 2 + stripIndex b 2 + 1))]

private theorem separationCharacter_swap (a b : ChartIndex) :
    separationCharacter b a = -separationCharacter a b := by
  have he (k : Fin 3) :
      separationSign (stripIndex b k) (stripIndex a k) =
        -separationSign (stripIndex a k) (stripIndex b k) :=
    separationSign_swap _ _
  unfold separationCharacter
  simp only [he]
  ext i
  fin_cases i <;> dsimp <;> ring

private def separationExponents (a b : ChartIndex) : Fin 3 → ℤ :=
  separationCharacter a b ᵥ* a2ConeMatrix a.1 a.2

private theorem separationExponents_eq_sum (a b : ChartIndex) (j : Fin 3) :
    separationExponents a b j =
      ∑ k, stripValue (stripIndex a k) (stripIndex b k)
        (pencil k (fun i ↦ a2ConeMatrix a.1 a.2 i j)) := by
  simp [separationExponents, separationCharacter, Matrix.vecMul, dotProduct,
    Fin.sum_univ_succ, stripValue, pencil, coneMatrix_last]
  ring

private theorem separationExponents_nonneg (a b : ChartIndex) (j : Fin 3) :
    0 ≤ separationExponents a b j := by
  rw [separationExponents_eq_sum]
  exact Finset.sum_nonneg fun k _ ↦ stripValue_nonneg (ray_strip_bounds a j k)

private theorem transition_nonneg_of_exponent_zero (a b : ChartIndex) (j : Fin 3)
    (hzero : separationExponents a b j = 0) : ∀ i, 0 ≤ transitionMatrix a b i j := by
  apply transition_nonneg_of_bounds a b j
  intro k
  apply stripValue_zero_bounds (ray_strip_bounds a j k)
  rw [separationExponents_eq_sum] at hzero
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ ↦ stripValue_nonneg (ray_strip_bounds a j k))).mp hzero k (Finset.mem_univ k)

private theorem separationExponents_pos_of_transition_neg
    (a b : ChartIndex) (i j : Fin 3) (hneg : transitionMatrix a b i j < 0) :
    0 < separationExponents a b j := by
  have hn := separationExponents_nonneg a b j
  by_contra h
  have hz : separationExponents a b j = 0 := by omega
  exact (not_lt_of_ge (transition_nonneg_of_exponent_zero a b j hz i)) hneg

private theorem separationExponents_transition (a b : ChartIndex) :
    separationExponents b a ᵥ* transitionMatrix a b = -separationExponents a b := by
  rw [separationExponents, separationCharacter_swap, Matrix.vecMul_vecMul,
    coneMatrix_mul_transitionMatrix]
  simp [separationExponents, Matrix.neg_vecMul]

private theorem separationExponents_cancel (a b : ChartIndex) (j : Fin 3) :
    separationExponents a b j +
      ∑ i, separationExponents b a i * transitionMatrix a b i j = 0 := by
  have h := congrFun (separationExponents_transition a b) j
  change (∑ i, separationExponents b a i * transitionMatrix a b i j) =
    -separationExponents a b j at h
  omega

private def character (a : Fin 3 → ℤ) (z : RawCoordinates) : ℂ :=
  ∏ j, z j ^ a j

private theorem character_contDiff (a : Fin 3 → ℤ) (ha : ∀ j, 0 ≤ a j) (n : ℕ∞ω) :
    ContDiff ℂ n (character a) := by
  apply contDiff_prod
  intro j _
  have he : (fun z : RawCoordinates ↦ z j ^ a j) =
      (fun z : RawCoordinates ↦ z j ^ (a j).toNat) := by
    funext z
    conv_lhs => rw [← Int.toNat_of_nonneg (ha j), zpow_natCast]
  rw [he]
  exact (contDiff_apply ℂ ℂ j).pow _

private theorem characters_mul_on_coordinateTorus
    (A : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℤ)
    (h : ∀ j, a j + ∑ i, b i * A i j = 0)
    {z : RawCoordinates} (hz : z ∈ coordinateTorus) :
    character a z * character b (monomial A z) = 1 := by
  have he := congrFun
    (monomial_comp_on_coordinateTorus (fun _ j : Fin 3 ↦ b j) A hz) 0
  change character b (monomial A z) = ∏ j, z j ^ ∑ i, b i * A i j at he
  rw [he]
  unfold character
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ j, z j ^ a j * z j ^ ∑ i, b i * A i j) = ∏ _j : Fin 3, (1 : ℂ) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [← zpow_add₀ (hz j), h j, zpow_zero]
    _ = 1 := by simp

private theorem characters_mul_on_domain
    (A : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℤ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (h : ∀ j, a j + ∑ i, b i * A i j = 0) :
    EqOn (fun z ↦ character a z * character b (monomial A z)) (fun _ ↦ 1)
      (monomialDomain A) := by
  have he : EqOn (fun z ↦ character a z * character b (monomial A z)) (fun _ ↦ 1)
      (monomialDomain A ∩ coordinateTorus) :=
    fun _ hz ↦ characters_mul_on_coordinateTorus A a b h hz.2
  refine he.of_subset_closure ?_ continuousOn_const Set.inter_subset_left
    (coordinateTorus_isDense.open_subset_closure_inter (monomialDomain_isOpen A))
  exact (character_contDiff a ha 0).continuous.continuousOn.mul
    ((character_contDiff b hb 0).continuous.comp_continuousOn
      (monomial_contDiffOn A 0).continuousOn)

private def overlapGraph (A : Matrix (Fin 3) (Fin 3) ℤ) :
    Set (RawCoordinates × RawCoordinates) :=
  {p | p.1 ∈ monomialDomain A ∧ monomial A p.1 = p.2}

private theorem overlapGraph_isClosed
    (A : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℤ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hcancel : ∀ j, a j + ∑ i, b i * A i j = 0)
    (hpos : ∀ i j, A i j < 0 → 0 < a j) : IsClosed (overlapGraph A) := by
  let P : RawCoordinates × RawCoordinates → ℂ := fun p ↦ character a p.1 * character b p.2
  have hP : Continuous P :=
    ((character_contDiff a ha 0).continuous.comp continuous_fst).mul
      ((character_contDiff b hb 0).continuous.comp continuous_snd)
  have hsubset : overlapGraph A ⊆ {p | P p = 1} := by
    intro p hp
    change character a p.1 * character b p.2 = 1
    rw [← hp.2]
    exact characters_mul_on_domain A a b ha hb hcancel hp.1
  apply isClosed_of_closure_subset
  intro p hp
  have hPeq : P p = 1 := closure_minimal hsubset (isClosed_eq hP continuous_const) hp
  have hD : p.1 ∈ monomialDomain A := by
    intro i j hij hz
    have hchar : character a p.1 = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hz, zero_zpow _ (ne_of_gt (hpos i j hij))]
    change character a p.1 * character b p.2 = 1 at hPeq
    simp [hchar] at hPeq
  refine ⟨hD, ?_⟩
  let : (𝓝[overlapGraph A] p).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hf : ContinuousAt (fun q : RawCoordinates × RawCoordinates ↦ monomial A q.1) p :=
    ((monomial_contDiffOn A 0).continuousOn.continuousAt
      ((monomialDomain_isOpen A).mem_nhds hD)).comp continuous_fst.continuousAt
  have he : (fun q : RawCoordinates × RawCoordinates ↦ monomial A q.1) =ᶠ[𝓝[overlapGraph A] p]
      Prod.snd := by
    filter_upwards [self_mem_nhdsWithin (s := overlapGraph A) (a := p)] with q hq
    exact hq.2
  exact tendsto_nhds_unique hf.continuousWithinAt
    (continuous_snd.continuousAt.continuousWithinAt.congr' he.symm)

private theorem chartOverlapGraph_isClosed (a b : ChartIndex) :
    IsClosed (overlapGraph (transitionMatrix a b)) :=
  overlapGraph_isClosed (transitionMatrix a b)
    (separationExponents a b) (separationExponents b a)
    (separationExponents_nonneg a b) (separationExponents_nonneg b a)
    (separationExponents_cancel a b) (separationExponents_pos_of_transition_neg a b)

/-- Closedness of every Laurent overlap graph makes the infinite gluing Hausdorff. -/
public theorem t2Space : T2Space Carrier := by
  constructor
  intro x y hxy
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective x
  obtain ⟨b, w, rfl⟩ := inclusion_jointly_surjective y
  have hn : (z, w) ∈ (overlapGraph (transitionMatrix a b))ᶜ := by
    intro h
    apply hxy
    exact (inclusion_eq_iff a b z w).mpr ⟨by simpa using h.1, h.2⟩
  obtain ⟨U, V, hU, hV, hz, hw, hUV⟩ :=
    isOpen_prod_iff.mp (chartOverlapGraph_isClosed a b).isOpen_compl z w hn
  refine ⟨inclusion a '' U, inclusion b '' V,
    (inclusion_isOpenEmbedding a).isOpenMap _ hU,
    (inclusion_isOpenEmbedding b).isOpenMap _ hV,
    Set.mem_image_of_mem _ hz, Set.mem_image_of_mem _ hw, ?_⟩
  apply Set.disjoint_left.mpr
  rintro q ⟨u, hu, hau⟩ ⟨v, hv, hbv⟩
  have he := (inclusion_eq_iff a b u v).mp (hau.trans hbv.symm)
  exact hUV (show (u, v) ∈ U ×ˢ V from ⟨hu, hv⟩) ⟨by simpa using he.1, he.2⟩

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
