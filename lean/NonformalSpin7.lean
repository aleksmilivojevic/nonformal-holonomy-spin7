import Init.Omega

/-!
This file formalizes the algebraic and logical deductions used in the
nonformal Spin(7) construction.  Differential geometry, de Rham theory,
Armstrong's theorem, Wang's classification, and DGMS formality are not in
Lean's core library.  They therefore occur only as named fields of explicit
input structures near the end of the file.  There are no global axioms.
-/

namespace NonformalSpin7

universe u v w

abbrev Pred (X : Type u) := X → Prop

/-! ## Additive cosets and their full indeterminacy -/

structure AdditiveCore (V : Type u) where
  zero : V
  add : V → V → V
  neg : V → V
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  add_comm : ∀ x y, add x y = add y x
  zero_add : ∀ x, add zero x = x
  add_zero : ∀ x, add x zero = x
  add_neg : ∀ x, add x (neg x) = zero

structure AdditiveSubset {V : Type u} (A : AdditiveCore V) where
  mem : Pred V
  zero_mem : mem A.zero
  add_mem : ∀ {x y}, mem x → mem y → mem (A.add x y)
  neg_mem : ∀ {x}, mem x → mem (A.neg x)

def affineCoset {V : Type u} (A : AdditiveCore V)
    (I : AdditiveSubset A) (representative x : V) : Prop :=
  ∃ i, I.mem i ∧ x = A.add representative i

theorem eq_neg_of_add_eq_zero {V : Type u} (A : AdditiveCore V)
    {x i : V} (h : A.add x i = A.zero) : x = A.neg i := by
  calc
    x = A.add x A.zero := (A.add_zero x).symm
    _ = A.add x (A.add i (A.neg i)) := by rw [A.add_neg i]
    _ = A.add (A.add x i) (A.neg i) := (A.add_assoc x i (A.neg i)).symm
    _ = A.add A.zero (A.neg i) := by rw [h]
    _ = A.neg i := A.zero_add (A.neg i)

theorem zero_mem_affineCoset_iff {V : Type u} (A : AdditiveCore V)
    (I : AdditiveSubset A) (representative : V) :
    affineCoset A I representative A.zero ↔ I.mem representative := by
  constructor
  · rintro ⟨i, hi, hzero⟩
    have hrep : representative = A.neg i :=
      eq_neg_of_add_eq_zero A hzero.symm
    rw [hrep]
    exact I.neg_mem hi
  · intro hrep
    refine ⟨A.neg representative, I.neg_mem hrep, ?_⟩
    exact (A.add_neg representative).symm

theorem full_affine_coset_exclusion {V : Type u} (A : AdditiveCore V)
    (I : AdditiveSubset A) {representative : V}
    (outside : ¬ I.mem representative) :
    ¬ affineCoset A I representative A.zero := by
  intro hzero
  exact outside ((zero_mem_affineCoset_iff A I representative).mp hzero)

theorem translated_representative_exclusion {V : Type u}
    (A : AdditiveCore V) (I : AdditiveSubset A) {certified chosen : V}
    (certified_outside : ¬ I.mem certified)
    (same_affine_coset : affineCoset A I certified chosen) :
    ¬ I.mem chosen := by
  rintro hchosen
  rcases same_affine_coset with ⟨i, hi, hchosen_eq⟩
  apply certified_outside
  have hsum : I.mem (A.add chosen (A.neg i)) :=
    I.add_mem hchosen (I.neg_mem hi)
  have heq : A.add chosen (A.neg i) = certified := by
    calc
      A.add chosen (A.neg i) =
          A.add (A.add certified i) (A.neg i) := by rw [hchosen_eq]
      _ = A.add certified (A.add i (A.neg i)) :=
          A.add_assoc certified i (A.neg i)
      _ = A.add certified A.zero := by rw [A.add_neg i]
      _ = certified := A.add_zero certified
  rwa [heq] at hsum

/-! ## Projection and the exceptional-coordinate certificate -/

theorem exclusion_by_projection {V : Type u} {W : Type v}
    (project : V → W) (I : Pred V) (J : Pred W) {y : V}
    (indeterminacy_projects : ∀ x, I x → J (project x))
    (projected_certificate : ¬ J (project y)) : ¬ I y := by
  intro hy
  exact projected_certificate (indeterminacy_projects y hy)

theorem unequal_coordinate_certificate {V : Type u} {K : Type v}
    (first second : V → K) (I : Pred V) (y : V)
    (minusFour plusFour : K)
    (indeterminacy_has_equal_coordinates : ∀ x, I x → first x = second x)
    (first_coordinate : first y = minusFour)
    (second_coordinate : second y = plusFour)
    (coordinates_distinct : minusFour ≠ plusFour) : ¬ I y := by
  intro hy
  apply coordinates_distinct
  calc
    minusFour = first y := first_coordinate.symm
    _ = second y := indeterminacy_has_equal_coordinates y hy
    _ = plusFour := second_coordinate

structure ExceptionalCoordinates where
  v1 : Int
  v2 : Int
  v3 : Int
  v7 : Int
deriving DecidableEq, Repr

def yMMCoordinates : ExceptionalCoordinates :=
  { v1 := -4, v2 := 4, v3 := 0, v7 := 0 }

def projectedIndeterminacy (x : ExceptionalCoordinates) : Prop :=
  ∃ A B : Int,
    x.v1 = A ∧ x.v2 = A ∧ x.v3 = -B ∧ x.v7 = B

theorem yMM_not_in_projected_indeterminacy :
    ¬ projectedIndeterminacy yMMCoordinates := by
  rintro ⟨A, B, h1, h2, _h3, _h7⟩
  have hneg : (-4 : Int) = A := h1
  have hpos : (4 : Int) = A := h2
  have impossible : (-4 : Int) = 4 := hneg.trans hpos.symm
  have unequal : (-4 : Int) ≠ 4 := by decide
  exact unequal impossible

theorem exceptional_coordinate_certificate {V : Type u}
    (project : V → ExceptionalCoordinates) (I : Pred V) (y : V)
    (indeterminacy_projects :
      ∀ x, I x → projectedIndeterminacy (project x))
    (representative_coordinates : project y = yMMCoordinates) :
    ¬ I y := by
  apply exclusion_by_projection project I projectedIndeterminacy
      indeterminacy_projects
  intro h
  rw [representative_coordinates] at h
  exact yMM_not_in_projected_indeterminacy h

/-! The doubled toric support values and Fulton's intersection sign. -/

def aOneWallIntersection (ell : Int) : Int := -(0 + 0 - 2 * ell)

def middleWallIntersection (ell L : Int) : Int :=
  -(ell + ell - 0 - L)

theorem toric_support_sign_certificate (ell L : Int)
    (ell_positive : 0 < ell) (scale_separation : 2 * ell < L) :
    aOneWallIntersection ell = 2 * ell ∧
    0 < aOneWallIntersection ell ∧
    middleWallIntersection ell L = L - 2 * ell ∧
    0 < middleWallIntersection ell L := by
  simp [aOneWallIntersection, middleWallIntersection]
  omega

/-! ## Transfer from the old manifold to the finite quotient -/

structure QuotientTransferData (Old : Type u) (Quotient : Type v) where
  oldIndeterminacy : Pred Old
  projectedQuotientIndeterminacy : Pred Old
  quotientIndeterminacy : Pred Quotient
  uEmbed : Old → Quotient
  uProject : Quotient → Old
  project_embed : ∀ y, uProject (uEmbed y) = y
  quotient_projects :
    ∀ q, quotientIndeterminacy q → projectedQuotientIndeterminacy (uProject q)
  projected_le_old :
    ∀ y, projectedQuotientIndeterminacy y → oldIndeterminacy y

theorem quotient_indeterminacy_transfer
    {Old : Type u} {Quotient : Type v}
    (D : QuotientTransferData Old Quotient) {y : Old}
    (old_excluded : ¬ D.oldIndeterminacy y) :
    ¬ D.quotientIndeterminacy (D.uEmbed y) := by
  intro hq
  apply old_excluded
  apply D.projected_le_old y
  have hp := D.quotient_projects (D.uEmbed y) hq
  rwa [D.project_embed y] at hp

/-! ## Gysin transfer through the resolution -/

structure GysinFormulaData where
  Base : Type u
  Resolved : Type v
  BaseLeft : Type w
  BaseRight : Type w
  ResolvedLeft : Type w
  ResolvedRight : Type w
  baseAdd : Base → Base → Base
  resolvedAdd : Resolved → Resolved → Resolved
  baseLeftTerm : BaseLeft → Base
  baseRightTerm : BaseRight → Base
  resolvedLeftTerm : ResolvedLeft → Resolved
  resolvedRightTerm : ResolvedRight → Resolved
  pull : Base → Resolved
  gysin : Resolved → Base
  gysinLeftParameter : ResolvedLeft → BaseLeft
  gysinRightParameter : ResolvedRight → BaseRight
  gysin_pull : ∀ x, gysin (pull x) = x
  gysin_add : ∀ x y, gysin (resolvedAdd x y) = baseAdd (gysin x) (gysin y)
  gysin_left : ∀ r,
    gysin (resolvedLeftTerm r) = baseLeftTerm (gysinLeftParameter r)
  gysin_right : ∀ q,
    gysin (resolvedRightTerm q) = baseRightTerm (gysinRightParameter q)

def GysinFormulaData.baseIndeterminacy (D : GysinFormulaData)
    (x : D.Base) : Prop :=
  ∃ r q, x = D.baseAdd (D.baseLeftTerm r) (D.baseRightTerm q)

def GysinFormulaData.resolvedIndeterminacy (D : GysinFormulaData)
    (x : D.Resolved) : Prop :=
  ∃ r q, x = D.resolvedAdd (D.resolvedLeftTerm r) (D.resolvedRightTerm q)

theorem gysin_maps_full_indeterminacy (D : GysinFormulaData)
    {x : D.Resolved} (hx : D.resolvedIndeterminacy x) :
    D.baseIndeterminacy (D.gysin x) := by
  rcases hx with ⟨r, q, hx⟩
  refine ⟨D.gysinLeftParameter r, D.gysinRightParameter q, ?_⟩
  calc
    D.gysin x = D.gysin
        (D.resolvedAdd (D.resolvedLeftTerm r) (D.resolvedRightTerm q)) := by
          rw [hx]
    _ = D.baseAdd (D.gysin (D.resolvedLeftTerm r))
        (D.gysin (D.resolvedRightTerm q)) := D.gysin_add _ _
    _ = D.baseAdd
        (D.baseLeftTerm (D.gysinLeftParameter r))
        (D.baseRightTerm (D.gysinRightParameter q)) := by
          rw [D.gysin_left r, D.gysin_right q]

theorem gysin_indeterminacy_transfer (D : GysinFormulaData)
    {y : D.Base} (base_excluded : ¬ D.baseIndeterminacy y) :
    ¬ D.resolvedIndeterminacy (D.pull y) := by
  intro hr
  apply base_excluded
  have hpush := gysin_maps_full_indeterminacy D hr
  rwa [D.gysin_pull y] at hpush

/-! ## The infinite-dihedral normal-generation calculation -/

inductive DInf where
  | translation : Int → DInf
  | reflection : Int → DInf
deriving DecidableEq, Repr

namespace DInf

def one : DInf := .translation 0
def S : DInf := .translation 1
def R : DInf := .reflection 0

def mul : DInf → DInf → DInf
  | .translation m, .translation n => .translation (m + n)
  | .translation m, .reflection n => .reflection (m + n)
  | .reflection m, .translation n => .reflection (m - n)
  | .reflection m, .reflection n => .translation (m - n)

def inv : DInf → DInf
  | .translation n => .translation (-n)
  | .reflection n => .reflection n

def SR : DInf := mul S R

theorem mul_assoc (a b c : DInf) : mul (mul a b) c = mul a (mul b c) := by
  cases a <;> cases b <;> cases c <;> simp [mul] <;> omega

theorem one_mul (a : DInf) : mul one a = a := by
  cases a <;> simp [one, mul]

theorem mul_one (a : DInf) : mul a one = a := by
  cases a <;> simp [one, mul]

theorem inv_mul (a : DInf) : mul (inv a) a = one := by
  cases a <;> simp [inv, mul, one] <;> omega

theorem mul_inv (a : DInf) : mul a (inv a) = one := by
  cases a <;> simp [inv, mul, one] <;> omega

theorem reflection_square : mul R R = one := by
  simp [R, one, mul]

theorem dihedral_relation : mul (mul R S) R = inv S := by
  simp [R, S, mul, inv]

theorem sr_mul_r : mul SR R = S := by
  simp [SR, S, R, mul]

structure NormalSubgroup where
  mem : Pred DInf
  one_mem : mem one
  mul_mem : ∀ {x y}, mem x → mem y → mem (mul x y)
  inv_mem : ∀ {x}, mem x → mem (inv x)
  conjugate_mem : ∀ {g x}, mem x → mem (mul (mul g x) (inv g))

private theorem nonnegative_translation_mem (N : NormalSubgroup)
    (hS : N.mem S) : ∀ n : Nat, N.mem (.translation (Int.ofNat n))
  | 0 => by simpa [one] using N.one_mem
  | n + 1 => by
      have h := N.mul_mem (nonnegative_translation_mem N hS n) hS
      change N.mem (.translation (Int.ofNat n + 1)) at h
      have heq : Int.ofNat n + 1 = Int.ofNat (n + 1) := by simp
      rw [heq] at h
      exact h

theorem translation_mem (N : NormalSubgroup) (hS : N.mem S)
    (n : Int) : N.mem (.translation n) := by
  cases n with
  | ofNat k => exact nonnegative_translation_mem N hS k
  | negSucc k =>
      have hp := nonnegative_translation_mem N hS (k + 1)
      have hi := N.inv_mem hp
      change N.mem (.translation (-(Int.ofNat (k + 1)))) at hi
      have heq : -(Int.ofNat (k + 1)) = Int.negSucc k := by
        simpa using (Int.negSucc_coe k).symm
      rw [heq] at hi
      exact hi

theorem reflection_mem (N : NormalSubgroup) (hS : N.mem S)
    (hR : N.mem R) (n : Int) : N.mem (.reflection n) := by
  have h := N.mul_mem (translation_mem N hS n) hR
  change N.mem (.reflection (n + 0)) at h
  simpa using h

theorem normal_generation (N : NormalSubgroup)
    (hR : N.mem R) (hSR : N.mem SR) : ∀ g : DInf, N.mem g := by
  have hS : N.mem S := by
    rw [← sr_mul_r]
    exact N.mul_mem hSR hR
  intro g
  cases g with
  | translation n => exact translation_mem N hS n
  | reflection n => exact reflection_mem N hS hR n

end DInf

/-! ## Armstrong and holonomy interfaces -/

structure ArmstrongInput where
  fixedPointNormalSubgroup : DInf.NormalSubgroup
  reflection_has_fixed_point : fixedPointNormalSubgroup.mem DInf.R
  shifted_reflection_has_fixed_point : fixedPointNormalSubgroup.mem DInf.SR
  CoverSimplyConnected : Prop
  ActionDiscontinuous : Prop
  QuotientSimplyConnected : Prop
  ResolutionSimplyConnected : Prop
  cover_simply_connected : CoverSimplyConnected
  action_discontinuous : ActionDiscontinuous
  armstrong_theorem :
    CoverSimplyConnected → ActionDiscontinuous →
      (∀ g, fixedPointNormalSubgroup.mem g) → QuotientSimplyConnected
  resolution_preserves_pi_one :
    QuotientSimplyConnected → ResolutionSimplyConnected

theorem ArmstrongInput.quotient_simply_connected (D : ArmstrongInput) :
    D.QuotientSimplyConnected := by
  apply D.armstrong_theorem D.cover_simply_connected D.action_discontinuous
  exact DInf.normal_generation D.fixedPointNormalSubgroup
    D.reflection_has_fixed_point D.shifted_reflection_has_fixed_point

theorem ArmstrongInput.resolution_simply_connected (D : ArmstrongInput) :
    D.ResolutionSimplyConnected :=
  D.resolution_preserves_pi_one D.quotient_simply_connected

theorem holonomy_alternative_elimination
    {HolonomySpin7 HolonomySU4 HolonomySp2 HolonomySp1xSp1 : Prop}
    {Kahler Formal : Prop}
    (classification :
      HolonomySpin7 ∨ HolonomySU4 ∨ HolonomySp2 ∨ HolonomySp1xSp1)
    (su4_kahler : HolonomySU4 → Kahler)
    (sp2_kahler : HolonomySp2 → Kahler)
    (sp1_product_kahler : HolonomySp1xSp1 → Kahler)
    (dgms : Kahler → Formal) (nonformal : ¬ Formal) : HolonomySpin7 := by
  rcases classification with h7 | hsu | hsp | hprod
  · exact h7
  · exact False.elim (nonformal (dgms (su4_kahler hsu)))
  · exact False.elim (nonformal (dgms (sp2_kahler hsp)))
  · exact False.elim (nonformal (dgms (sp1_product_kahler hprod)))

/-! ## An end-to-end Massey pipeline -/

structure MasseyPipelineInput where
  Old : Type u
  Quotient : Type v
  Resolved : Type w
  Scalar : Type u
  oldAdd : AdditiveCore Old
  oldIndeterminacy : AdditiveSubset oldAdd
  coordinateRepresentative : Old
  oldRepresentative : Old
  v1Coordinate : Old → Scalar
  v2Coordinate : Old → Scalar
  minusFour : Scalar
  plusFour : Scalar
  minusFour_ne_plusFour : minusFour ≠ plusFour
  old_indeterminacy_equal_v1_v2 :
    ∀ x, oldIndeterminacy.mem x → v1Coordinate x = v2Coordinate x
  coordinate_representative_v1 :
    v1Coordinate coordinateRepresentative = minusFour
  coordinate_representative_v2 :
    v2Coordinate coordinateRepresentative = plusFour
  averaged_representative_same_coset :
    affineCoset oldAdd oldIndeterminacy coordinateRepresentative oldRepresentative
  quotientTransfer : QuotientTransferData Old Quotient
  quotient_old_indeterminacy_agrees :
    ∀ x, quotientTransfer.oldIndeterminacy x ↔ oldIndeterminacy.mem x
  resolvedAdd : AdditiveCore Resolved
  resolvedIndeterminacy : AdditiveSubset resolvedAdd
  pull : Quotient → Resolved
  gysin : Resolved → Quotient
  gysin_pull : ∀ x, gysin (pull x) = x
  gysin_maps_indeterminacy :
    ∀ x, resolvedIndeterminacy.mem x →
      quotientTransfer.quotientIndeterminacy (gysin x)

def MasseyPipelineInput.quotientRepresentative (D : MasseyPipelineInput) :
    D.Quotient := D.quotientTransfer.uEmbed D.oldRepresentative

def MasseyPipelineInput.finalRepresentative (D : MasseyPipelineInput) :
    D.Resolved := D.pull D.quotientRepresentative

theorem MasseyPipelineInput.coordinate_representative_excluded
    (D : MasseyPipelineInput) :
    ¬ D.oldIndeterminacy.mem D.coordinateRepresentative := by
  exact unequal_coordinate_certificate D.v1Coordinate D.v2Coordinate
    D.oldIndeterminacy.mem D.coordinateRepresentative D.minusFour D.plusFour
    D.old_indeterminacy_equal_v1_v2 D.coordinate_representative_v1
    D.coordinate_representative_v2 D.minusFour_ne_plusFour

theorem MasseyPipelineInput.old_representative_excluded
    (D : MasseyPipelineInput) :
    ¬ D.oldIndeterminacy.mem D.oldRepresentative := by
  exact translated_representative_exclusion D.oldAdd D.oldIndeterminacy
    D.coordinate_representative_excluded D.averaged_representative_same_coset

theorem MasseyPipelineInput.quotient_representative_excluded
    (D : MasseyPipelineInput) :
    ¬ D.quotientTransfer.quotientIndeterminacy D.quotientRepresentative := by
  apply quotient_indeterminacy_transfer D.quotientTransfer
  intro hold
  exact D.old_representative_excluded
    ((D.quotient_old_indeterminacy_agrees D.oldRepresentative).mp hold)

theorem MasseyPipelineInput.final_representative_excluded
    (D : MasseyPipelineInput) :
    ¬ D.resolvedIndeterminacy.mem D.finalRepresentative := by
  intro hfinal
  apply D.quotient_representative_excluded
  have hpush := D.gysin_maps_indeterminacy D.finalRepresentative hfinal
  change D.quotientTransfer.quotientIndeterminacy
    (D.gysin (D.pull D.quotientRepresentative)) at hpush
  rwa [D.gysin_pull D.quotientRepresentative] at hpush

theorem MasseyPipelineInput.full_massey_coset_excludes_zero
    (D : MasseyPipelineInput) :
    ¬ affineCoset D.resolvedAdd D.resolvedIndeterminacy
      D.finalRepresentative D.resolvedAdd.zero :=
  full_affine_coset_exclusion D.resolvedAdd D.resolvedIndeterminacy
    D.final_representative_excluded

/-! ## Explicit boundary between formalized deductions and geometry -/

structure GeometricInput where
  massey : MasseyPipelineInput
  topology : ArmstrongInput
  Smooth : Prop
  Compact : Prop
  ProperResolution : Prop
  RegularLocusDiffeomorphism : Prop
  TorsionFreeSpin7 : Prop
  Formal : Prop
  Kahler : Prop
  HolonomySpin7 : Prop
  HolonomySU4 : Prop
  HolonomySp2 : Prop
  HolonomySp1xSp1 : Prop
  smooth : Smooth
  compact : Compact
  proper_resolution : ProperResolution
  regular_locus_diffeomorphism : RegularLocusDiffeomorphism
  torsion_free_spin7 : TorsionFreeSpin7
  formal_cdga_forces_zero_massey :
    Formal → affineCoset massey.resolvedAdd massey.resolvedIndeterminacy
      massey.finalRepresentative massey.resolvedAdd.zero
  berger_simons_wang_de_rham :
    Compact → TorsionFreeSpin7 → topology.ResolutionSimplyConnected →
      HolonomySpin7 ∨ HolonomySU4 ∨ HolonomySp2 ∨ HolonomySp1xSp1
  su4_is_kahler : HolonomySU4 → Kahler
  sp2_is_kahler : HolonomySp2 → Kahler
  sp1_product_is_kahler : HolonomySp1xSp1 → Kahler
  dgms_formality : Kahler → Formal

theorem GeometricInput.nonformal (D : GeometricInput) : ¬ D.Formal := by
  intro hformal
  exact D.massey.full_massey_coset_excludes_zero
    (D.formal_cdga_forces_zero_massey hformal)

theorem GeometricInput.simply_connected (D : GeometricInput) :
    D.topology.ResolutionSimplyConnected :=
  D.topology.resolution_simply_connected

theorem GeometricInput.full_holonomy_spin7 (D : GeometricInput) :
    D.HolonomySpin7 := by
  apply holonomy_alternative_elimination
    (D.berger_simons_wang_de_rham D.compact D.torsion_free_spin7
      D.simply_connected)
    D.su4_is_kahler D.sp2_is_kahler D.sp1_product_is_kahler
    D.dgms_formality D.nonformal

structure VerifiedConclusion (D : GeometricInput) : Prop where
  smooth : D.Smooth
  compact : D.Compact
  proper_resolution : D.ProperResolution
  regular_locus_diffeomorphism : D.RegularLocusDiffeomorphism
  torsion_free_spin7 : D.TorsionFreeSpin7
  full_massey_coset_excludes_zero :
    ¬ affineCoset D.massey.resolvedAdd D.massey.resolvedIndeterminacy
      D.massey.finalRepresentative D.massey.resolvedAdd.zero
  nonformal : ¬ D.Formal
  simply_connected : D.topology.ResolutionSimplyConnected
  full_holonomy_spin7 : D.HolonomySpin7

theorem verified_conclusion (D : GeometricInput) : VerifiedConclusion D where
  smooth := D.smooth
  compact := D.compact
  proper_resolution := D.proper_resolution
  regular_locus_diffeomorphism := D.regular_locus_diffeomorphism
  torsion_free_spin7 := D.torsion_free_spin7
  full_massey_coset_excludes_zero := D.massey.full_massey_coset_excludes_zero
  nonformal := D.nonformal
  simply_connected := D.simply_connected
  full_holonomy_spin7 := D.full_holonomy_spin7

#print axioms full_affine_coset_exclusion
#print axioms yMM_not_in_projected_indeterminacy
#print axioms toric_support_sign_certificate
#print axioms quotient_indeterminacy_transfer
#print axioms gysin_indeterminacy_transfer
#print axioms DInf.normal_generation
#print axioms holonomy_alternative_elimination
#print axioms verified_conclusion

end NonformalSpin7
