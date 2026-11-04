import MeraConstraints.HiddenGraph.StrongFaceSplitting
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Measurable evaluation on A1 root graphs

Jointly measurable local mechanisms give measurable evaluation by induction
along the observed DAG. This statement allows the raw split graph, including
empty or single-child latent roots, without imposing A2.
-/

namespace MeraConstraints.HiddenGraph.StrongFaceSplitting.RootSCM

open MeasureTheory

variable {n : ℕ} {R : Type*} {G : RootGraph n R} {val : Fin n → Type*}
  (M : RootSCM G val) [∀ i, MeasurableSpace (val i)]
  [∀ r, MeasurableSpace (M.rootValue r)] [∀ i, MeasurableSpace (M.privateNoise i)]

def MechanismsMeasurable : Prop := ∀ i : Fin n,
  Measurable (fun z : PaAssign G.observed val i ×
      ((∀ r : {r // i ∈ G.children r}, M.rootValue r.val) × M.privateNoise i) =>
    M.F i z.1 z.2.1 z.2.2)

theorem eval_apply_measurable (hF : M.MechanismsMeasurable) (i : Fin n) :
    Measurable (fun x : (∀ r, M.rootValue r) × (∀ i, M.privateNoise i) => M.eval x.1 x.2 i) := by
  have hp : Measurable (fun x : (∀ r, M.rootValue r) × (∀ i, M.privateNoise i) =>
      PaAssign.restrict (G := G.observed) (M.eval x.1 x.2) i) := by
    apply measurable_pi_iff.mpr
    intro j
    exact eval_apply_measurable hF j.val
  have hr : Measurable (fun x : (∀ r, M.rootValue r) × (∀ i, M.privateNoise i) =>
      fun r : {r // i ∈ G.children r} => x.1 r.val) :=
    measurable_pi_iff.mpr fun r => (measurable_pi_apply r.val).comp measurable_fst
  have hm := (hF i).comp (hp.prodMk (hr.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have heq : (fun x : (∀ r, M.rootValue r) × (∀ i, M.privateNoise i) => M.eval x.1 x.2 i) =
      (fun x => M.F i (PaAssign.restrict (G := G.observed) (M.eval x.1 x.2) i)
        (fun r => x.1 r.val) (x.2 i)) := funext fun x => M.eval_eq x.1 x.2 i
  rw [heq]
  exact hm
termination_by i.val
decreasing_by exact G.observed.parents_lt j.property

theorem eval_measurable (hF : M.MechanismsMeasurable) :
    Measurable (fun x : (∀ r, M.rootValue r) × (∀ i, M.privateNoise i) => M.eval x.1 x.2) :=
  measurable_pi_iff.mpr (M.eval_apply_measurable hF)

end MeraConstraints.HiddenGraph.StrongFaceSplitting.RootSCM
