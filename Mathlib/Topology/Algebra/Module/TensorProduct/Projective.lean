/-
Copyright (c) 2026 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Pacholski
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Topology.Algebra.Module.LocallyConvex
@[expose] public section

open scoped TensorProduct

section Semiring

variable {R M N : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable (M N)

variable (R) in
/-- Type synonym for the projective tensor product of topological modules. -/
public def ProjectiveTensorProduct := M ⊗[R] N

@[inherit_doc] scoped[TensorProduct] notation:100 M:100 " ⊗[" R "]π " N:101 =>
  ProjectiveTensorProduct R M N

end Semiring

namespace TensorProduct

section TopologicalSpace

variable {R M N : Type*}
variable [CommSemiring R] [PartialOrder R] [TopologicalSpace R]
variable [AddCommGroup M] [Module R M] [TopologicalSpace M] [LocallyConvexSpace R M]
variable [AddCommGroup N] [Module R N] [TopologicalSpace N] [LocallyConvexSpace R N]

instance : AddCommGroup (M ⊗[R]π N) := addCommGroup
instance : Module R (M ⊗[R]π N) := instModule

/-- The projective topology on `X ⊗[𝕜]π Y` is defined as the supremum of all topologies
making the space a locally convex topological module such that `tmul` is continuous. -/
instance instTopologicalSpaceProjectiveTensorProduct : TopologicalSpace (M ⊗[R]π N) :=
  sSup { t : TopologicalSpace (M ⊗[R] N) |
    letI := t
    IsTopologicalAddGroup (M ⊗[R] N) ∧
    ContinuousSMul R (M ⊗[R] N) ∧
    LocallyConvexSpace R (M ⊗[R] N) ∧
    Continuous (fun (p : M × N) ↦ p.1 ⊗ₜ[R] p.2) }

end TopologicalSpace

end TensorProduct
