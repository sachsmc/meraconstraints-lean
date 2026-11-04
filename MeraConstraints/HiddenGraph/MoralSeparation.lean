import MeraConstraints.HiddenGraph.AncestralBlanket

/-!
# Separation in the original hidden DAG's ancestral moral graph

The criterion is purely graphical. First retain the observed ancestors of
`X ∪ Y ∪ Z` and every latent root with a child among those ancestors. Then
make each retained parent-child pair adjacent and marry the parents of each
retained child. Finally remove the observed conditioning vertices `Z`.
`MoralSeparated` says no remaining undirected walk joins `X` to `Y`.

This uses ancestral moral separation as the specification of graphical
separation; it does not define separation by conditional independence or by
the local Markov equations. An active-trail presentation is not developed
here. Latent roots are included explicitly, rather than replacing an entire
observed district by a clique without a graph proof.

The last theorem supplies that proof where it is needed: at c-degree at
most one, all unconditioned variables in a retained district's kernel family
lie on the same side of any moral-graph cut. A shared root supplies the
connecting paths; a degree-zero district uses its singleton's moral family.
-/

namespace MeraConstraints.HiddenGraph

variable {n ℓ : ℕ} (G : Graph n ℓ)

noncomputable def observedAncestors (S : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ∃ j ∈ S, ObservedAncestor G i j

@[simp] theorem mem_observedAncestors (S : Finset (Fin n)) (i : Fin n) :
    i ∈ observedAncestors G S ↔ ∃ j ∈ S, ObservedAncestor G i j := by
  classical
  simp [observedAncestors]

theorem subset_observedAncestors (S : Finset (Fin n)) : S ⊆ observedAncestors G S :=
  fun i hi => (mem_observedAncestors G S i).mpr ⟨i, hi, observedAncestor_refl G i⟩

theorem observedAncestors_ancestral (S : Finset (Fin n)) :
    ObservedAncestral G (observedAncestors G S) := by
  intro i hi j hji
  obtain ⟨k, hk, hik⟩ := (mem_observedAncestors G S i).mp hi
  exact (mem_observedAncestors G S j).mpr ⟨k, hk, observedAncestor_trans G hji hik⟩

/-- A parent in the original hidden DAG; all children are observed by A1. -/
def FullParent (x : Vertex (n := n) (ℓ := ℓ)) (i : Fin n) : Prop :=
  match x with
  | .inl j => j ∈ G.observed.parents i
  | .inr u => i ∈ G.children u

/-- All directed arrows of the original graph, including latent roots. -/
def FullEdge (x y : Vertex (n := n) (ℓ := ℓ)) : Prop :=
  match y with
  | .inl i => FullParent G x i
  | .inr _ => False

abbrev FullAncestor := Relation.ReflTransGen (FullEdge G)

theorem fullAncestor_from_observed (i : Fin n) {y : Vertex (n := n) (ℓ := ℓ)}
    (h : FullAncestor G (.inl i) y) : ∃ j, y = .inl j ∧ ObservedAncestor G i j := by
  induction h with
  | refl => exact ⟨i, rfl, observedAncestor_refl G i⟩
  | @tail y z _ hyz ih =>
    obtain ⟨j, rfl, hij⟩ := ih
    cases z with
    | inl k => exact ⟨k, rfl, hij.tail hyz⟩
    | inr u => exact hyz.elim

theorem fullAncestor_observed_iff (i j : Fin n) :
    FullAncestor G (.inl i) (.inl j) ↔ ObservedAncestor G i j := by
  constructor
  · intro h
    obtain ⟨k, hk, hik⟩ := fullAncestor_from_observed G i h
    have hjk := Sum.inl.inj hk
    simpa only [hjk] using hik
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail hstep

theorem fullAncestor_latent_observed_iff (u : Fin ℓ) (j : Fin n) :
    FullAncestor G (.inr u) (.inl j) ↔ ∃ i, i ∈ G.children u ∧ ObservedAncestor G i j := by
  constructor
  · intro h
    rcases h.cases_head with heq | ⟨x, hux, hxj⟩
    · cases heq
    · cases x with
      | inl i => exact ⟨i, hux, (fullAncestor_observed_iff G i j).mp hxj⟩
      | inr v => exact hux.elim
  · rintro ⟨i, hi, hij⟩
    have hstep : FullEdge G (.inr u) (.inl i) := hi
    exact ((fullAncestor_observed_iff G i j).mpr hij).head hstep

def MoralVertex (A : Finset (Fin n)) : Vertex (n := n) (ℓ := ℓ) → Prop
  | .inl i => i ∈ A
  | .inr u => ∃ i ∈ A, i ∈ G.children u

/-- The retained vertices are exactly the ancestors in the original full
DAG of the queried observed set, including the required latent roots. -/
theorem moralVertex_ancestral_iff (S : Finset (Fin n)) (x : Vertex (n := n) (ℓ := ℓ)) :
    MoralVertex G (observedAncestors G S) x ↔ ∃ j ∈ S, FullAncestor G x (.inl j) := by
  cases x with
  | inl i =>
    constructor
    · intro hi
      obtain ⟨j, hj, hij⟩ := (mem_observedAncestors G S i).mp hi
      exact ⟨j, hj, (fullAncestor_observed_iff G i j).mpr hij⟩
    · rintro ⟨j, hj, hij⟩
      exact (mem_observedAncestors G S i).mpr ⟨j, hj, (fullAncestor_observed_iff G i j).mp hij⟩
  | inr u =>
    constructor
    · rintro ⟨i, hi, hiu⟩
      obtain ⟨j, hj, hij⟩ := (mem_observedAncestors G S i).mp hi
      exact ⟨j, hj, (fullAncestor_latent_observed_iff G u j).mpr ⟨i, hiu, hij⟩⟩
    · rintro ⟨j, hj, huj⟩
      obtain ⟨i, hiu, hij⟩ := (fullAncestor_latent_observed_iff G u j).mp huj
      exact ⟨i, (mem_observedAncestors G S i).mpr ⟨j, hj, hij⟩, hiu⟩

def ConditionedVertex (Z : Finset (Fin n)) : Vertex (n := n) (ℓ := ℓ) → Prop
  | .inl i => i ∈ Z
  | .inr _ => False

def MoralAllowed (A Z : Finset (Fin n)) (x : Vertex (n := n) (ℓ := ℓ)) : Prop :=
  MoralVertex G A x ∧ ¬ ConditionedVertex Z x

/-- Undirected parent-child and co-parent adjacency. Loops are harmless for
walk separation and simplify the co-parent case. -/
def MoralRelated (A : Finset (Fin n)) (x y : Vertex (n := n) (ℓ := ℓ)) : Prop :=
  (∃ i ∈ A, x = .inl i ∧ FullParent G y i) ∨
  (∃ i ∈ A, y = .inl i ∧ FullParent G x i) ∨
    ∃ i ∈ A, FullParent G x i ∧ FullParent G y i

theorem moralRelated_symm (A : Finset (Fin n)) {x y : Vertex (n := n) (ℓ := ℓ)}
    (h : MoralRelated G A x y) : MoralRelated G A y x := by
  rcases h with h | h | ⟨i, hi, hx, hy⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨i, hi, hy, hx⟩)

def MoralStep (A Z : Finset (Fin n)) (x y : Vertex (n := n) (ℓ := ℓ)) : Prop :=
  MoralAllowed G A Z x ∧ MoralAllowed G A Z y ∧ MoralRelated G A x y

abbrev MoralConnected (A Z : Finset (Fin n)) := Relation.ReflTransGen (MoralStep G A Z)

def MoralCut (A Z : Finset (Fin n)) (side : Vertex (n := n) (ℓ := ℓ) → Bool) : Prop :=
  ∀ x y, MoralAllowed G A Z x → MoralAllowed G A Z y → MoralRelated G A x y → side x = side y

/-- The ancestral moral-graph separation criterion, including disjointness
of the three observed sets. It contains no probability-law premise. -/
def MoralSeparated (X Y Z : Finset (Fin n)) : Prop :=
  Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z ∧
    ∀ i ∈ X, ∀ j ∈ Y,
      ¬ MoralConnected G (observedAncestors G (X ∪ Y ∪ Z)) Z (.inl i) (.inl j)

theorem moralCut_constant_on_connected (A Z : Finset (Fin n))
    (side : Vertex (n := n) (ℓ := ℓ) → Bool) (hcut : MoralCut G A Z side)
    {x y : Vertex (n := n) (ℓ := ℓ)} (h : MoralConnected G A Z x y) : side x = side y := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hcut _ _ hstep.1 hstep.2.1 hstep.2.2)

/-- A finite coloring certificate also proves the no-walk separation
predicate. Together with `moralSeparated_cut` this checks both directions
between path separation and the cut used in the probability proof. -/
theorem moralSeparated_of_cut (X Y Z : Finset (Fin n))
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (side : Vertex (n := n) (ℓ := ℓ) → Bool)
    (hX : ∀ i ∈ X, side (.inl i) = false) (hY : ∀ j ∈ Y, side (.inl j) = true)
    (hcut : MoralCut G (observedAncestors G (X ∪ Y ∪ Z)) Z side) : MoralSeparated G X Y Z := by
  refine ⟨hXY, hXZ, hYZ, ?_⟩
  intro i hi j hj hpath
  have heq := moralCut_constant_on_connected G _ Z side hcut hpath
  rw [hX i hi, hY j hj] at heq
  exact Bool.false_ne_true heq

/-- No connecting walk yields a literal two-sided cut of the original
ancestral moral graph. The cut is constructed from reachability from `X`. -/
theorem moralSeparated_cut (X Y Z : Finset (Fin n)) (hsep : MoralSeparated G X Y Z) :
    ∃ side : Vertex (n := n) (ℓ := ℓ) → Bool,
      (∀ i ∈ X, side (.inl i) = false) ∧ (∀ j ∈ Y, side (.inl j) = true) ∧
        MoralCut G (observedAncestors G (X ∪ Y ∪ Z)) Z side := by
  classical
  let A := observedAncestors G (X ∪ Y ∪ Z)
  let reach := fun x : Vertex (n := n) (ℓ := ℓ) => ∃ i ∈ X, MoralConnected G A Z (.inl i) x
  let side := fun x => if reach x then false else true
  refine ⟨side, ?_, ?_, ?_⟩
  · intro i hi
    exact if_pos ⟨i, hi, Relation.ReflTransGen.refl⟩
  · intro j hj
    exact if_neg (by rintro ⟨i, hi, hij⟩; exact hsep.2.2.2 i hi j hj hij)
  · intro x y hx hy hxy
    have heq : reach x ↔ reach y := by
      constructor
      · rintro ⟨i, hi, hix⟩
        exact ⟨i, hi, hix.tail ⟨hx, hy, hxy⟩⟩
      · rintro ⟨i, hi, hiy⟩
        exact ⟨i, hi, hiy.tail ⟨hy, hx, moralRelated_symm G A hxy⟩⟩
    simp only [side, heq]

/-- Variables read by the ordinary margin of the kernel on `D ∩ A`. -/
def KernelFamily (A : Finset (Fin n)) (d : DistrictId G) (j : Fin n) : Prop :=
  ∃ i ∈ A, observedDistrict G i = d ∧ (j = i ∨ j ∈ G.observed.parents i)

theorem kernelFamily_mem_ancestral (A : Finset (Fin n)) (hA : ObservedAncestral G A)
    (d : DistrictId G) (j : Fin n) (hj : KernelFamily G A d j) : j ∈ A := by
  obtain ⟨i, hi, _, rfl | hji⟩ := hj
  · exact hi
  · exact hA i hi j (observedAncestor_of_parent G hji)

/-- No kernel family can straddle a moral-graph cut outside the conditioning
set. This is where the degree-one star/singleton structure is used. -/
theorem kernelFamily_same_side (A Z : Finset (Fin n)) (hA : ObservedAncestral G A)
    (hdegree : ∀ x, cDegree G x ≤ 1) (side : Vertex (n := n) (ℓ := ℓ) → Bool)
    (hcut : MoralCut G A Z side) (d : DistrictId G) (j k : Fin n)
    (hj : KernelFamily G A d j) (hk : KernelFamily G A d k) (hjZ : j ∉ Z) (hkZ : k ∉ Z) :
    side (.inl j) = side (.inl k) := by
  have hjA := kernelFamily_mem_ancestral G A hA d j hj
  have hkA := kernelFamily_mem_ancestral G A hA d k hk
  obtain ⟨v, hvA, hvd, hjv⟩ := hj
  obtain ⟨w, hwA, hwd, hkw⟩ := hk
  have hvw : Connected G (.inl v) (.inl w) :=
    (districtOf_eq_iff G _ _).mp (hvd.trans hwd.symm)
  by_cases hu : ∃ u, v ∈ G.children u
  · obtain ⟨u, hvu⟩ := hu
    have hwu : w ∈ G.children u := child_of_cDegree_le_one G u w (hdegree _)
      (Relation.EqvGen.trans _ _ _ (connected_child G u v hvu) hvw)
    have huA : MoralAllowed G A Z (.inr u) := ⟨⟨v, hvA, hvu⟩, id⟩
    have hju : MoralRelated G A (.inl j) (.inr u) := by
      rcases hjv with hjv | hjv
      · exact Or.inl ⟨v, hvA, congrArg Sum.inl hjv, hvu⟩
      · exact Or.inr (Or.inr ⟨v, hvA, hjv, hvu⟩)
    have hku : MoralRelated G A (.inl k) (.inr u) := by
      rcases hkw with hkw | hkw
      · exact Or.inl ⟨w, hwA, congrArg Sum.inl hkw, hwu⟩
      · exact Or.inr (Or.inr ⟨w, hwA, hkw, hwu⟩)
    exact (hcut (.inl j) (.inr u) ⟨hjA, hjZ⟩ huA hju).trans
      (hcut (.inl k) (.inr u) ⟨hkA, hkZ⟩ huA hku).symm
  · have hwv : w = v := Sum.inl.inj (connected_observed_eq_of_no_latent_parent G v hu hvw)
    subst w
    by_cases hjk : j = k
    · subst k
      rfl
    · have hjkRel : MoralRelated G A (.inl j) (.inl k) := by
        rcases hjv with hjv | hjv <;> rcases hkw with hkv | hkv
        · exact (hjk (hjv.trans hkv.symm)).elim
        · exact Or.inl ⟨v, hvA, congrArg Sum.inl hjv, hkv⟩
        · exact Or.inr (Or.inl ⟨v, hvA, congrArg Sum.inl hkv, hjv⟩)
        · exact Or.inr (Or.inr ⟨v, hvA, hjv, hkv⟩)
      exact hcut (.inl j) (.inl k) ⟨hjA, hjZ⟩ ⟨hkA, hkZ⟩ hjkRel

end MeraConstraints.HiddenGraph
