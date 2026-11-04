import MeraConstraints.HiddenGraph.HLP

/-!
# HLP absorption preserves every observed evaluation

Proposition `prop:hlp`, reverse structural direction: remove the added edge
`a → b` by moving `a`'s private disturbance into a chosen shared latent root.
All observed parents of `a` are already available to `b`, and every latent
parent of `a` is a latent parent of `b`. Consequently `b` reconstructs the
same value of `a` before evaluating its original mechanism.

The proof checks the actual recursive equations at `a`, at `b`, and at every
other vertex. Uniqueness then gives equality of complete observed assignments
for every original latent/private input realization. Input types may be
infinite and no probability or c-degree assumption is needed.
`HiddenGraph.HLPMeasure`, `HiddenGraph.HLPInputs` and `Completeness.HLP`
separately prove measurability, full mutual independence after grouping and
probability-model equivalence.
-/

namespace MeraConstraints.HiddenGraph.HLP

variable {n ℓ : ℕ} {G : HiddenGraph.Graph n ℓ} {a b : Fin n} {hab : a < b}
  {val : Fin n → Type*} (M : HiddenGraph.SCM (addEdge G a b hab) val)

/-- The value reconstructed at `b` uses only its permitted original parents
and is exactly the source model's value at `a`. -/
theorem reconstructed_a_eq
    (hpa : G.observed.parents a ⊆ G.observed.parents b)
    (s : Fin ℓ) (u : ∀ j, M.latentValue j) (ε : ∀ i, M.privateNoise i) :
    M.F a (PaAssign.restrict
        (parentWitness M b (PaAssign.restrict (G := G.observed) (M.eval u ε) b)) a)
      (fun j => (absorbLatents M s u ε j.val).1)
      (absorbLatents M s u ε s).2 = M.eval u ε a := by
  rw [parentWitness_b_restrict_a M hpa]
  simpa only [absorbLatents, ite_true] using (M.eval_eq u ε a).symm

/-- HLP reverse pointwise simulation, for the explicit parent-restricted
absorption model and the explicit original-input encoding. -/
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
