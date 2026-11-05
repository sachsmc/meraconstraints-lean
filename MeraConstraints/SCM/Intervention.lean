import MeraConstraints.SCM.ResponseFunction

/-!
# The response function variable transformation preserves interventions

Remark 1 (`rmk1`) says that the response function variable transformation gives
the same values of all variables under any intervention on observed variables,
including no intervention. Here an intervention on a set of target variables
replaces their structural equations by constants and keeps the inputs. For each
value `u` of the inputs, the response functions induced by `u`, with the targets'
response functions replaced by the constants, give the values of the intervened
model (`eval_intervene_eq_evalR`). The induced response functions do not depend on
the targets or the constants, so they serve for every intervention at once. The
statement is for each fixed `u`; it makes no assumption on the distribution of the
inputs.

This is the model with one input per observed variable from `SCM/Basic.lean`. The
version for hidden variables DAGs is in `HiddenGraph.Intervention`.
-/

namespace MeraConstraints

variable {n : ℕ} {G : CausalDAG n} {val : Fin n → Type*}

/-- Replace the response functions of the target variables by constants. -/
def interveneProfile (r : RespAssign G val) (targets : Finset (Fin n))
    (setTo : FullAssign val) : RespAssign G val :=
  fun i pa => if i ∈ targets then setTo i else r i pa

theorem evalR_intervene_at_target (r : RespAssign G val)
    (targets : Finset (Fin n)) (setTo : FullAssign val) (i : Fin n)
    (hi : i ∈ targets) :
    evalR (interveneProfile r targets setTo) i = setTo i := by
  rw [evalR_eq]
  simp [interveneProfile, hi]

namespace SCM

/-- The intervention that sets the target variables to the constants `setTo`: their
structural equations are replaced by constants, and the input types are kept. -/
def intervene (M : SCM G val) (targets : Finset (Fin n))
    (setTo : FullAssign val) : SCM G val where
  exo := M.exo
  exoNonempty := M.exoNonempty
  F := fun i pa u => if i ∈ targets then setTo i else M.F i pa u

theorem respOf_intervene (M : SCM G val) (targets : Finset (Fin n))
    (setTo : FullAssign val) (u : ∀ i, M.exo i) :
    (M.intervene targets setTo).respOf u =
      interveneProfile (M.respOf u) targets setTo := rfl

/-- Remark 1 (`rmk1`) for a fixed value `u` of the inputs and any set of targets.
The response functions `M.respOf u` do not depend on the intervention. -/
theorem eval_intervene_eq_evalR (M : SCM G val) (u : ∀ i, M.exo i)
    (targets : Finset (Fin n)) (setTo : FullAssign val) :
    (M.intervene targets setTo).eval u =
      evalR (interveneProfile (M.respOf u) targets setTo) := by
  rw [SCM.eval_eq_evalR, respOf_intervene]

/-- Two values of the inputs that induce the same response functions give the same
values of the observed variables under every intervention. -/
theorem interventions_eq_of_same_profile (M : SCM G val)
    (u u' : ∀ i, M.exo i) (h : M.respOf u = M.respOf u')
    (targets : Finset (Fin n)) (setTo : FullAssign val) :
    (M.intervene targets setTo).eval u = (M.intervene targets setTo).eval u' := by
  rw [eval_intervene_eq_evalR, eval_intervene_eq_evalR, h]

end SCM
end MeraConstraints
