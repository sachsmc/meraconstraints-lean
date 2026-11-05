import MeraConstraints.HiddenGraph.HLP

/-!
# Moving the private noise of `a` preserves the values

This is the reverse direction of Proposition 5 (`prop:hlp`) for a fixed value of
the inputs. To remove the edge `a → b`, the private noise of `a` is moved into a
common unobserved parent `s` of `a` and `b` (`absorb`). The parents of `a` among
the observed variables are parents of `b`, and every unobserved parent of `a` is
a parent of `b`. So `b` can recompute the value of `a` from what it sees and the
moved noise (`reconstructed_a_eq`), and then apply its own structural equation.

`eval_absorb` shows that the model `absorb` has the same values of the observed
variables as the original model, for every value of the inputs. The proof checks
the structural equations at `a`, at `b`, and at every other variable, and the
values are the unique solution of the equations. The input types are arbitrary
and the statement does not involve probabilities or the c-degree. That the
generated distributions agree is shown in `HLPInputs.lean`, `HLPMeasure.lean`
and `Completeness/HLP.lean`.
-/

namespace MeraConstraints.HiddenGraph.HLP

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {a b : Fin n} {hab : a < b}
  {val : Fin n → Type*} (M : HiddenGraph.SCM (addEdge G a b hab) val)

/-- Computed from the parents of `b` and the moved noise, the equation of `a`
gives the value of `a`. -/
theorem reconstructed_a_eq
    (hpa : G.observed.parents a ⊆ G.observed.parents b)
    (s : Fin ℓ) (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) :
    M.F a (PaAssign.restrict
        (parentWitness M b (PaAssign.restrict (G := G.observed) (M.eval u ε) b)) a)
      (fun j => (absorbLatents M s u ε j.val).1)
      (absorbLatents M s u ε s).2 = M.eval u ε a := by
  rw [parentWitness_b_restrict_a M hpa]
  simpa only [absorbLatents, ite_true] using (M.eval_eq u ε a).symm

/-- The model `absorb`, at the inputs `absorbLatents` and `absorbPrivate`, has the
same values of the observed variables as `M` at its inputs. -/
theorem eval_absorb
    (hpa : G.observed.parents a ⊆ G.observed.parents b)
    (hLat : ∀ j : Fin ℓ, a ∈ G.children j → b ∈ G.children j)
    (s : Fin ℓ) (hsa : a ∈ G.children s) (hsb : b ∈ G.children s)
    (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) :
    (absorb M hLat s hsa hsb).eval (absorbLatents M s u ε) (absorbPrivate M ε) =
      M.eval u ε := by
  symm
  apply HiddenGraph.SCM.eval_unique
  intro i
  by_cases hia : i = a
  · subst i
    simp only [absorb, absorbLatents, dite_true, ite_true]
    rw [parentWitness_restrict_of_ne M (M.eval u ε) a (ne_of_lt hab)]
    exact M.eval_eq u ε a
  · by_cases hib : i = b
    · subst i
      simp only [absorb, dif_neg hia, dite_true]
      rw [reconstructed_a_eq M hpa s u ε]
      rw [updatedWitness_restrict_b M (M.eval u ε) (M.eval u ε a) rfl]
      simpa only [absorbLatents, absorbPrivate, if_neg hia] using M.eval_eq u ε b
    · simp only [absorb, dif_neg hia, dif_neg hib]
      rw [parentWitness_restrict_of_ne M (M.eval u ε) i hib]
      simpa only [absorbLatents, absorbPrivate, if_neg hia] using M.eval_eq u ε i

end MeraConstraints.HiddenGraph.HLP
