import MeraConstraints.SCM.ResponseFunction

/-!
# Response reduction preserves interventions

Remark `rmk1` asserts that response-variable transformation preserves the
values of every observed variable under **any** intervention, including no
intervention. The reused `SCM.eval_eq_evalR` theorem previously covered only
the unmodified equations. Here an intervention replaces the mechanisms of
the selected observed vertices by constants, keeping the same latent inputs.

For each fixed original latent assignment, the same induced response profile
works simultaneously for every choice of intervention targets and values.
This is a pointwise statement about potential outcomes. It neither identifies
them from observations nor places an unrestricted distribution on profiles
at higher c-degree.
-/

namespace MeraConstraints

variable {n : ℕ} {G : CausalDAG n} {val : Fin n → Type*}

/-- Replace the response functions of intervention targets by constants. -/
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

/-- Surgical intervention: replace the selected structural equations, while
retaining the input types and the actual latent assignment. -/
def intervene (M : SCM G val) (targets : Finset (Fin n))
    (setTo : FullAssign val) : SCM G val where
  exo := M.exo
  exoNonempty := M.exoNonempty
  F := fun i pa u => if i ∈ targets then setTo i else M.F i pa u

theorem respOf_intervene (M : SCM G val) (targets : Finset (Fin n))
    (setTo : FullAssign val) (u : ∀ i, M.exo i) :
    (M.intervene targets setTo).respOf u =
      interveneProfile (M.respOf u) targets setTo := rfl

/-- Pointwise content of Remark `rmk1`, including arbitrary target sets.
The profile on the right is induced before choosing the intervention. -/
theorem eval_intervene_eq_evalR (M : SCM G val) (u : ∀ i, M.exo i)
    (targets : Finset (Fin n)) (setTo : FullAssign val) :
    (M.intervene targets setTo).eval u =
      evalR (interveneProfile (M.respOf u) targets setTo) := by
  rw [SCM.eval_eq_evalR, respOf_intervene]

/-- Two original latent assignments in the same canonical response-profile
class remain indistinguishable under every observed intervention. -/
theorem interventions_eq_of_same_profile (M : SCM G val)
    (u u' : ∀ i, M.exo i) (h : M.respOf u = M.respOf u')
    (targets : Finset (Fin n)) (setTo : FullAssign val) :
    (M.intervene targets setTo).eval u = (M.intervene targets setTo).eval u' := by
  rw [eval_intervene_eq_evalR, eval_intervene_eq_evalR, h]

end SCM
end MeraConstraints
