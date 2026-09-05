# Lean verification of the nonformal Spin(7) argument

`NonformalSpin7.lean` is a Lean 4.8 formalization of the algebraic and
logical spine of `nonformal_spin7_construction.tex`. It is intentionally not
presented as a formalization of Joyce's analytic resolution theorem or of the
foundational differential geometry. Those subjects are not available in the
Lean core library used by this project.

## Kernel-checked deductions

The file verifies the following statements.

1. `zero_mem_affineCoset_iff` proves that zero belongs to the full affine
   coset `y + I` exactly when `y` belongs to `I`, for an additive subgroup
   `I`.
   Consequently, `full_affine_coset_exclusion` proves that excluding the
   representative from the entire indeterminacy subgroup excludes zero from
   the entire Massey coset. This is stronger than proving only that one
   representative is nonzero.

2. `translated_representative_exclusion` proves that replacing a defining
   system by another representative in the same affine coset preserves the
   exclusion from indeterminacy. This models the passage from the explicit
   Martín--Merchán defining system to the averaged equivariant defining
   system.

3. `yMM_not_in_projected_indeterminacy` checks the exceptional-coordinate
   certificate
   
   \[
   (-4,4,0,0)\notin
   \{(A,A,-B,B):A,B\in\mathbb Z\}.
   \]
   
   The contradiction uses the independent `v1` and `v2` coordinates: it
   would require both `A = -4` and `A = 4`. The concrete proof is by
   decidable integer equality and has no axiomatic dependencies.

4. `exclusion_by_projection`, `unequal_coordinate_certificate`, and
   `exceptional_coordinate_certificate` formalize the inference from the
   projected indeterminacy calculation to exclusion from the full
   indeterminacy. The generic theorem uses an arbitrary coefficient type and
   only the inequality between the two displayed coordinates. It therefore
   models the real-coefficient calculation, rather than merely an integral
   span calculation.

5. `quotient_indeterminacy_transfer` formalizes the `u`-summand projection
   used for the finite quotient. If the quotient representative lay in the
   quotient indeterminacy, its (u)-projection would lie in a specified
   subspace of the old indeterminacy, contradicting the old certificate.

6. `GysinFormulaData` records the retraction and the two projection-formula
   identities separately. `gysin_maps_full_indeterminacy` proves that the
   Gysin map sends every sum of the two resolved indeterminacy terms to the
   corresponding sum of the two quotient terms.
   `gysin_indeterminacy_transfer` then proves that a representative excluded
   before resolution remains excluded after pullback to the resolution.

7. The namespace `DInf` defines the infinite dihedral group in normal form as
   the elements (S^n) and (S^nR), proves the group identities and
   (RSR=S^{-1}), and proves `normal_generation`. Thus any normal subgroup
   containing the two fixed-point reflections `R` and `SR` contains
   `S = (SR)R` and every element of the infinite dihedral group. This is the group-theoretic
   step in the Armstrong argument.

8. `holonomy_alternative_elimination` checks the final case distinction. From
   the alternatives
   
   \[
   \operatorname{Spin}(7),\quad SU(4),\quad Sp(2),\quad
   Sp(1)\times Sp(1),
   \]
   
   the three Kähler alternatives contradict nonformality through DGMS, so
   the remaining alternative is full holonomy `Spin(7)`.

9. `toric_support_sign_certificate` checks the Fulton sign using
   doubled support values. It proves
   
   \[
   -(0+0-2\ell)=2\ell>0,
   \qquad
   -(\ell+\ell-0-L)=L-2\ell>0
   \]
   
   from `0 < ell` and `2 * ell < L`.

10. `MasseyPipelineInput` combines the coordinate certificate, change of
    representative, quotient projection, Gysin transfer, and full affine
    coset lemma. Its theorem `full_massey_coset_excludes_zero` is the complete
    kernel-checked deduction from those named inputs.

## Geometric input boundary

`GeometricInput` is the explicit boundary between the formalized deductions
and the cited geometry. Its fields state, rather than conceal, the following
external inputs:

- the cohomology projection and indeterminacy calculations;
- the quotient decomposition and its `u`-projection;
- the Gysin retraction and projection formula;
- the simply connected covering space and discontinuous dihedral action;
- Armstrong's orbit-space theorem and preservation of the fundamental group
  under the fibrewise resolution;
- smoothness and compactness of the resolved manifold;
- properness of the resolution map and its diffeomorphism over the regular
  locus;
- existence of the torsion-free Spin(7) structure;
- the de Rham--Berger--Simons--Wang holonomy alternatives;
- the fact that the three proper alternatives are Kähler;
- DGMS formality of compact Kähler manifolds; and
- the standard implication that formality forces every defined Massey
  product to contain zero.

The theorem `verified_conclusion` derives, from one value of this explicit
interface, all clauses of the main theorem represented in the formal model:
smoothness, compactness, properness of the resolution, the regular-locus
diffeomorphism, existence of the torsion-free Spin(7) structure, exclusion of
zero from the full Massey coset, nonformality, simple connectivity, and full
Spin(7) holonomy. The file contains no `axiom`, `sorry`, or `admit`
declaration.
Universal fields of `GeometricInput` are hypotheses of the theorem, not
global Lean axioms.

The final `#print axioms` commands make the trust boundary machine-visible.
The main assembled theorem reports only Lean's standard propositional
extensionality principle. The integer arithmetic tactic used for the toric
certificate reports Lean's standard quotient and choice principles. No
project-specific mathematical assertion enters through an undeclared axiom.

## Deliberate limitations

This artifact does not define smooth manifolds, differential forms, CDGAs,
Massey products from cochain-level defining systems, Riemannian holonomy, or
Joyce's analytic gluing theory. It therefore does not claim a first-principles
formal verification of those theories. Instead, it formalizes every finite
algebraic and logical implication used after the manuscript's geometric and
cohomological inputs have been established. Extending the verification below
this boundary requires substantial Mathlib developments that are not present
in the core-only environment.

## Verification command

With Lean 4.8.0 available through `elan`, run the following command from the
project root:

```sh
lean +leanprover/lean4:v4.8.0 lean/NonformalSpin7.lean
```
