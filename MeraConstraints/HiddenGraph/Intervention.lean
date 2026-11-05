import MeraConstraints.HiddenGraph.Model
import MeraConstraints.SCM.Intervention
import MeraConstraints.CompactDistrict

/-!
# Interventions on a structural model

Remark 1 (`rmk1`) says that the response function variable transformation gives
the same values of all variables under any intervention on observed variables.
Here an intervention on a set of observed variables replaces their structural
equations by constants (`SCM.intervene`). The response functions of the
intervened model are those of the original model with the same coordinates
replaced by constants (`responseProfile_intervene`). So the response functions
computed from the inputs do not depend on the intervention, and the values under
any intervention are obtained by evaluating them (`eval_intervene_eq_evalR`).

For a district `d`, fix its external parents and leave its members unchanged.
The values of the members are then `CompactDistrict.eval` of the profile of `d`
at the fixed values of the external parents
(`eval_intervene_restrict_eq_compact`). The same holds when all observed
variables outside the district are fixed, so fixing these or only the
external parents gives the same values of the members
(`eval_intervene_external_eq_complement`), which is used in the proof of
Proposition 2 (`causalprop`). These identities hold for every c-degree and
use no probability distribution.
-/

namespace MeraConstraints.HiddenGraph.SCM

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {val : Fin n → Type*}

/-- The structural model in which each variable in `targets` is set to its value
in `setTo`. -/
def intervene (M : HiddenGraph.SCM G val) (targets : Finset (Fin n))
    (setTo : FullAssign val) : HiddenGraph.SCM G val where
  latentValue := M.latentValue
  latentNonempty := M.latentNonempty
  privateNoise := M.privateNoise
  privateNonempty := M.privateNonempty
  F := fun i pa u ε => if i ∈ targets then setTo i else M.F i pa u ε

theorem responseProfile_intervene (M : HiddenGraph.SCM G val)
    (targets : Finset (Fin n)) (setTo : FullAssign val)
    (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) :
    (M.intervene targets setTo).responseProfile u ε =
      interveneProfile (M.responseProfile u ε) targets setTo := rfl

/-- The values under an intervention are obtained by evaluating the response
functions of the original model with the targets set. -/
theorem eval_intervene_eq_evalR (M : HiddenGraph.SCM G val)
    (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i)
    (targets : Finset (Fin n)) (setTo : FullAssign val) :
    (M.intervene targets setTo).eval u ε =
      evalR (interveneProfile (M.responseProfile u ε) targets setTo) := by
  rw [eval_eq_evalR, responseProfile_intervene]

theorem eval_intervene_at_target (M : HiddenGraph.SCM G val)
    (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i)
    (targets : Finset (Fin n)) (setTo : FullAssign val) (i : Fin n)
    (hi : i ∈ targets) :
    (M.intervene targets setTo).eval u ε i = setTo i := by
  rw [eval_intervene_eq_evalR]
  exact evalR_intervene_at_target _ targets setTo i hi

theorem interventions_eq_of_same_profile (M : HiddenGraph.SCM G val)
    (u u' : ∀ j, M.latentValue j) (ε ε' : ∀ i, M.privateNoise i)
    (h : M.responseProfile u ε = M.responseProfile u' ε')
    (targets : Finset (Fin n)) (setTo : FullAssign val) :
    (M.intervene targets setTo).eval u ε = (M.intervene targets setTo).eval u' ε' := by
  rw [eval_intervene_eq_evalR, eval_intervene_eq_evalR, h]

end MeraConstraints.HiddenGraph.SCM

namespace MeraConstraints.CompactDistrict

variable {n : ℕ} (G : CausalDAG n) (val : Fin n → Type*)
variable {D : Type*} [DecidableEq D] (block : Fin n → D) (d : D)

/-- The observed parents of the block `d` that are outside it. -/
noncomputable def externalTargets : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (IsExternalParent G block d)

omit [DecidableEq D] in
@[simp] theorem mem_externalTargets (j : Fin n) :
    j ∈ externalTargets G block d ↔ IsExternalParent G block d j := by
  classical
  simp [externalTargets]

/-- All observed variables outside the block `d`. -/
def complementTargets : Finset (Fin n) := Finset.univ.filter fun j => block j ≠ d

@[simp] theorem mem_complementTargets (j : Fin n) :
    j ∈ complementTargets block d ↔ block j ≠ d := by
  simp [complementTargets]

/-- If no member is fixed and all external parents are fixed, the values of the
members are `CompactDistrict.eval` of the profile of the block. -/
theorem evalR_intervene_eq_eval (r : RespAssign G val)
    (targets : Finset (Fin n)) (setTo : FullAssign val)
    (hmember : ∀ i : Member block d, i.val ∉ targets)
    (hexternal : ∀ j : ExternalParent G block d, j.val ∈ targets) :
    (fun i : Member block d => evalR (interveneProfile r targets setTo) i) =
      eval G val block d (fun i => r i) (fun j => setTo j) := by
  let output := evalR (interveneProfile r targets setTo)
  let x : Row G val block d := (fun i => output i, fun j => setTo j)
  have hx : Compatible G val block d x (fun i => r i) := by
    intro i
    have hpa : parentAssign G val block d x i = PaAssign.restrict output i := by
      funext j
      unfold parentAssign
      by_cases hj : block j = d
      · simp only [dif_pos hj]
        rfl
      · simp only [dif_neg hj]
        exact (evalR_intervene_at_target r targets setTo j
          (hexternal ⟨j, hj, ⟨i, i.property, j.property⟩⟩)).symm
    change r i (parentAssign G val block d x i) = output i
    rw [hpa]
    have hi := evalR_eq (interveneProfile r targets setTo) i.val
    simpa only [interveneProfile, if_neg (hmember i)] using hi.symm
  exact ((eval_eq_iff_compatible G val block d x (fun i => r i)).2 hx).symm

theorem evalR_intervene_external_eq_eval (r : RespAssign G val) (setTo : FullAssign val) :
    (fun i : Member block d =>
      evalR (interveneProfile r (externalTargets G block d) setTo) i) =
      eval G val block d (fun i => r i) (fun j => setTo j) := by
  apply evalR_intervene_eq_eval G val block d r _ setTo
  · intro i hi
    exact ((mem_externalTargets G block d i).1 hi).1 i.property
  · intro j
    exact (mem_externalTargets G block d j).2 j.property

theorem evalR_intervene_complement_eq_eval (r : RespAssign G val) (setTo : FullAssign val) :
    (fun i : Member block d =>
      evalR (interveneProfile r (complementTargets block d) setTo) i) =
      eval G val block d (fun i => r i) (fun j => setTo j) := by
  apply evalR_intervene_eq_eval G val block d r _ setTo
  · intro i hi
    exact ((mem_complementTargets block d i).1 hi) i.property
  · intro j
    exact (mem_complementTargets block d j).2 j.property.1

end MeraConstraints.CompactDistrict

namespace MeraConstraints.HiddenGraph.SCM

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {val : Fin n → Type*}
  [DecidableEq (HiddenGraph.DistrictId G)]

/-- Under an intervention that fixes the external parents of the district `d`
and no member, the values of the members are `CompactDistrict.eval` of the
profile of response functions of `d`. -/
theorem eval_intervene_restrict_eq_compact (M : HiddenGraph.SCM G val)
    (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i)
    (d : HiddenGraph.DistrictId G) (targets : Finset (Fin n)) (setTo : FullAssign val)
    (hmember : ∀ i : CompactDistrict.Member (HiddenGraph.observedDistrict G) d,
      i.val ∉ targets)
    (hexternal : ∀ j : CompactDistrict.ExternalParent G.observed
      (HiddenGraph.observedDistrict G) d, j.val ∈ targets) :
    (fun i : CompactDistrict.Member (HiddenGraph.observedDistrict G) d =>
      (M.intervene targets setTo).eval u ε i) =
      CompactDistrict.eval G.observed val (HiddenGraph.observedDistrict G) d
        (fun i => M.responseProfile u ε i) (fun j => setTo j) := by
  rw [eval_intervene_eq_evalR]
  exact CompactDistrict.evalR_intervene_eq_eval _ _ _ _ _ _ _ hmember hexternal

/-- Fixing only the external parents of `d` gives the same values of the
members. -/
theorem eval_intervene_external_eq_compact (M : HiddenGraph.SCM G val)
    (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i)
    (d : HiddenGraph.DistrictId G) (setTo : FullAssign val) :
    (fun i : CompactDistrict.Member (HiddenGraph.observedDistrict G) d =>
      (M.intervene (CompactDistrict.externalTargets G.observed
        (HiddenGraph.observedDistrict G) d) setTo).eval u ε i) =
      CompactDistrict.eval G.observed val (HiddenGraph.observedDistrict G) d
        (fun i => M.responseProfile u ε i) (fun j => setTo j) := by
  rw [eval_intervene_eq_evalR]
  exact CompactDistrict.evalR_intervene_external_eq_eval _ _ _ _ _ _

/-- Fixing all observed variables outside `d` gives the same values of the
members. -/
theorem eval_intervene_complement_eq_compact (M : HiddenGraph.SCM G val)
    (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i)
    (d : HiddenGraph.DistrictId G) (setTo : FullAssign val) :
    (fun i : CompactDistrict.Member (HiddenGraph.observedDistrict G) d =>
      (M.intervene (CompactDistrict.complementTargets
        (HiddenGraph.observedDistrict G) d) setTo).eval u ε i) =
      CompactDistrict.eval G.observed val (HiddenGraph.observedDistrict G) d
        (fun i => M.responseProfile u ε i) (fun j => setTo j) := by
  rw [eval_intervene_eq_evalR]
  exact CompactDistrict.evalR_intervene_complement_eq_eval _ _ _ _ _ _

/-- Fixing all observed variables outside `d` or only its external parents gives
the same values of the members. Used in the proof of Proposition 2
(`causalprop`). -/
theorem eval_intervene_external_eq_complement (M : HiddenGraph.SCM G val)
    (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i)
    (d : HiddenGraph.DistrictId G) (setTo : FullAssign val) :
    (fun i : CompactDistrict.Member (HiddenGraph.observedDistrict G) d =>
      (M.intervene (CompactDistrict.externalTargets G.observed
        (HiddenGraph.observedDistrict G) d) setTo).eval u ε i) =
    (fun i : CompactDistrict.Member (HiddenGraph.observedDistrict G) d =>
      (M.intervene (CompactDistrict.complementTargets
        (HiddenGraph.observedDistrict G) d) setTo).eval u ε i) := by
  rw [eval_intervene_external_eq_compact, eval_intervene_complement_eq_compact]

end MeraConstraints.HiddenGraph.SCM
