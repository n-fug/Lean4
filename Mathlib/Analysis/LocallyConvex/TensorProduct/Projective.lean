module

public import Mathlib.Analysis.Normed.Module.TensorProduct.ProjectiveSeminorm
public import Mathlib.Topology.Algebra.Module.TensorProduct.Projective

import Mathlib.Analysis.Seminorm

open TensorProduct Seminorm

variable {𝕜 X Y : Type*}

variable [NormedField 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [PolynormableSpace 𝕜 X]
variable [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y] [PolynormableSpace 𝕜 Y]

variable {ιX ιY : Type*}

variable (p : SeminormFamily 𝕜 X ιX) (q : SeminormFamily 𝕜 Y ιY)

noncomputable def ProjectiveSeminormFamily : SeminormFamily 𝕜 (X ⊗[𝕜]π Y) (ιX × ιY) := fun ⟨i, j⟩ ↦
  letI := AddGroupSeminorm.toSeminormedAddCommGroup (p i).toAddGroupSeminorm
  letI := AddGroupSeminorm.toSeminormedAddCommGroup (q j).toAddGroupSeminorm
  letI : NormedSpace 𝕜 X := ⟨fun a b ↦ ((p i).smul' a b).le⟩
  letI : NormedSpace 𝕜 Y := ⟨fun a b ↦ ((q j).smul' a b).le⟩
  projectiveSeminorm

-- noncomputable def projectiveSeminormTopology : TopologicalSpace (X ⊗[𝕜] Y) :=
--   (ProjectiveSeminormFamily p q).moduleFilterBasis.topology

lemma projectiveSeminormTopology_mem_sSup :
    (ProjectiveSeminormFamily p q).moduleFilterBasis.topology ∈ { t : TopologicalSpace (X ⊗[𝕜] Y) |
      letI := t
      IsTopologicalAddGroup (X ⊗[𝕜] Y) ∧
      ContinuousSMul 𝕜 (X ⊗[𝕜] Y) ∧
      LocallyConvexSpace 𝕜 (X ⊗[𝕜] Y) ∧
      Continuous (fun (p : X × Y) ↦ p.1 ⊗ₜ[𝕜] p.2) } := by
  -- letI := projectiveSeminormTopology p q
  -- have h_with : WithSeminorms (ProjectiveSeminormFamily p q) := ⟨rfl⟩
  -- refine ⟨h_with.topologicalAddGroup, h_with.continuousSMul, h_with.toLocallyConvexSpace, ?_⟩
  -- -- Prove continuity of tmul using the bounding lemma `projectiveSeminorm_tprod_le`
  -- rw [continuous_iff_continuousAt]
  -- intro ⟨x, y⟩
  -- (Insert the standard epsilon-delta bound using `projectiveSeminorm_tprod_le` here)
  sorry

theorem withSeminorms_projectiveTensorProduct : WithSeminorms (ProjectiveSeminormFamily p q)
    (topology := instTopologicalSpaceProjectiveTensorProduct) := by
  constructor
  apply le_antisymm
  · apply sSup_le
    rintro t ⟨h1, h2, h3, h4⟩
    sorry
  · have h_mem := projectiveSeminormTopology_mem_sSup p q
    exact le_sSup h_mem
