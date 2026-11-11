import Specs.Target
import Mathlib.Order.BooleanAlgebra.Basic
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Guard-synthesis specification audit

The target statements through Round 11 match their blueprint claims after unfolding
the synthesis definitions. The earlier mismatch between the weakest-guard
implication and the blueprint's iff has been resolved: the blueprint now
separates `synthesizeGuard_weakest` from `synthesizeGuard_adjunction`.
`blueprint_adjunction` checks the equivalence independently below.

The proof and compiler stubs in `Specs.Target` currently contain placeholders. None
of the proofs below invokes them: importing a placeholder must not turn an
audit into circular evidence. The Bool cases use kernel-checked `decide`;
the Prop proofs use conjunction and implication directly. The constructive
Bool instance below avoids the classical Boolean-to-Heyting adapter, and
the generic proofs avoid choice-dependent library shortcuts. Axiom inspection
must find neither `sorryAx` nor `Classical.choice` in any audit declaration.

Bool exhausts four state/target pairs and eight state/target/guard triples.
Prop checks arbitrary propositions, including all True/False combinations.
The explicit active witnesses show that the hypotheses are satisfiable with
a true state and a true guard. The rejected witnesses show that the validity
premise is meaningful and cannot simply be omitted.
-/

namespace CatSem.RedTeam

/-- The usual Bool order and implication, with a constructive adjunction proof.
This keeps all existing truth tables while avoiding the classical adapter. -/
local instance constructiveBool : HeytingAlgebra Bool :=
  HeytingAlgebra.ofHImp (fun a b => !a || b) (by decide)

/-- The full blueprint equivalence, proved without the target declarations. -/
theorem blueprint_adjunction {α : Type*} [HeytingAlgebra α] (a b g : α) :
    a ⊓ g ≤ b ↔ g ≤ synthesizeGuard a b := by
  exact le_himp_iff'.symm

/-- Exhaustive soundness check over all four Bool pairs. -/
theorem bool_sound (a b : Bool) : a ⊓ synthesizeGuard a b ≤ b := by
  cases a <;> cases b <;> decide

/-- Exhaustive weakest-guard check over all eight Bool triples. -/
theorem bool_weakest (a b g : Bool) (h : a ⊓ g ≤ b) :
    g ≤ synthesizeGuard a b := by
  revert h
  cases a <;> cases b <;> cases g <;> decide

/-- Check both directions of the separate adjunction target. -/
theorem bool_adjunction (a b g : Bool) :
    a ⊓ g ≤ b ↔ g ≤ synthesizeGuard a b := by
  cases a <;> cases b <;> cases g <;> decide

/-- Synthesis is not a constant guard: these are all four Bool outputs. -/
theorem bool_truth_table :
    synthesizeGuard false false = true ∧
    synthesizeGuard false true = true ∧
    synthesizeGuard true false = false ∧
    synthesizeGuard true true = true := by
  decide

/-- Every Bool state/target pair admits a valid guard. -/
theorem bool_valid_guard_exists (a b : Bool) : ∃ g : Bool, a ⊓ g ≤ b := by
  refine ⟨false, ?_⟩
  cases a <;> cases b <;> decide

/-- Both hypotheses and conclusions hold with an active state and guard. -/
theorem bool_active_witness :
    (true ⊓ true ≤ true) ∧
    (true ⊓ synthesizeGuard true true ≤ true) ∧
    (true ≤ synthesizeGuard true true) := by
  decide

/-- A false target forces a false guard when the state is true. -/
theorem bool_restrictive_witness :
    (true ⊓ false ≤ false) ∧ (false ≤ synthesizeGuard true false) := by
  decide

/-- A false state allows a true guard even for a false target. -/
theorem bool_false_state_witness :
    (false ⊓ true ≤ false) ∧ (true ≤ synthesizeGuard false false) := by
  decide

/-- Dropping validity would make weakest-guard optimality false. -/
theorem bool_rejected_guard :
    ¬ (true ⊓ true ≤ false) ∧ ¬ (true ≤ synthesizeGuard true false) := by
  decide

/-- Soundness for arbitrary propositions, using direct modus ponens. -/
theorem prop_sound (a b : Prop) : a ⊓ synthesizeGuard a b ≤ b := by
  change (a ∧ (a → b)) → b
  exact fun h => h.2 h.1

/-- Weakest-guard optimality for arbitrary propositions, using currying. -/
theorem prop_weakest (a b g : Prop) (h : a ⊓ g ≤ b) :
    g ≤ synthesizeGuard a b := by
  change g → a → b
  exact fun hg ha => h ⟨ha, hg⟩

/-- The full Prop adjunction is currying/uncurrying, with no classical cases. -/
theorem prop_adjunction (a b g : Prop) :
    a ⊓ g ≤ b ↔ g ≤ synthesizeGuard a b := by
  change ((a ∧ g) → b) ↔ (g → a → b)
  constructor
  · exact fun h hg ha => h ⟨ha, hg⟩
  · exact fun h hag => h hag.2 hag.1

/-- Every Prop state/target pair admits a valid guard. -/
theorem prop_valid_guard_exists (a b : Prop) : ∃ g : Prop, a ⊓ g ≤ b := by
  exact ⟨False, fun h => h.2.elim⟩

/-- Concrete non-vacuity with a true state, true guard, and true target. -/
theorem prop_active_witness :
    (True ⊓ True ≤ True) ∧
    (True ⊓ synthesizeGuard True True ≤ True) ∧
    (True ≤ synthesizeGuard True True) := by
  exact ⟨fun _ => True.intro, fun _ => True.intro, fun _ _ => True.intro⟩

/-- Concrete restrictive guard for a true state and false target. -/
theorem prop_restrictive_witness :
    (True ⊓ False ≤ False) ∧ (False ≤ synthesizeGuard True False) := by
  exact ⟨fun h => h.2, fun h _ => h⟩

/-- A false state makes the true guard valid even for a false target. -/
theorem prop_false_state_witness :
    (False ⊓ True ≤ False) ∧ (True ≤ synthesizeGuard False False) := by
  exact ⟨fun h => h.1, fun _ h => h⟩

/-- The same omitted-premise counterexample in Prop. -/
theorem prop_rejected_guard :
    ¬ (True ⊓ True ≤ False) ∧ ¬ (True ≤ synthesizeGuard True False) := by
  exact ⟨fun h => h ⟨True.intro, True.intro⟩,
    fun h => h True.intro True.intro⟩

/-!
## Round 2: CFG transfers

`CFGTransfer.gc` has the required orientation:
`T.post x ≤ b ↔ x ≤ T.pullback b`. Thus edge soundness and optimality follow
from this adjunction and the local Heyting adjunction. The branch theorem
requires both postconditions, so its synthesized guard is a meet. All three
CFG theorem statements match the corresponding blueprint nodes exactly.

Scope: this structure supplies an adjoint pair for a single edge. Round 3
adds identity and composition operations, checked below. It does not yet
encode a CFG, a presheaf, or Kripke-Joyal forcing semantics. The algebraic
blueprint claims need only the given transfer operations.

The four-element domain below is `Bool × Bool` with componentwise order.
Each transfer retains one coordinate in its postcondition and allows the
other coordinate freely in its pullback. Both maps are nonidentity and
nonconstant. Their Galois connections are checked by exhaustive cases.
The independent edge checks cover 32 soundness cases and 128 optimality
cases across the two transfers. The branch check covers all 256 quadruples.
-/

namespace Round2

/-- A finite Boolean algebra with two independent coordinates. -/
abbrev State := Bool × Bool

/-- `true` retains the first coordinate; `false` retains the second. -/
def keepCoordinate (first : Bool) : CFGTransfer State State where
  post x := if first then (x.1, false) else (false, x.2)
  pullback b := if first then (b.1, true) else (true, b.2)
  gc := by
    rintro ⟨x₁, x₂⟩ ⟨b₁, b₂⟩
    cases first <;> cases x₁ <;> cases x₂ <;> cases b₁ <;> cases b₂ <;> decide

/-- Neither map in either concrete transfer is the identity. -/
theorem transfer_nonidentity (first : Bool) :
    (keepCoordinate first).post ≠ id ∧ (keepCoordinate first).pullback ≠ id := by
  constructor
  · intro h
    have hf := congrFun h (true, true)
    cases first <;> cases hf
  · intro h
    have hf := congrFun h (false, false)
    cases first <;> cases hf

/-- Neither map collapses the domain to a constant. -/
theorem transfer_nonconstant (first : Bool) :
    (keepCoordinate first).post (false, false) ≠
      (keepCoordinate first).post (true, true) ∧
    (keepCoordinate first).pullback (false, false) ≠
      (keepCoordinate first).pullback (true, true) := by
  cases first <;> decide

/-- The full edge equivalence follows directly from the two adjunctions. -/
theorem edge_adjunction {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (a : α) (b : β) (g : α) :
    T.post (a ⊓ g) ≤ b ↔ g ≤ synthesizeEdgeGuard T a b := by
  exact (T.gc _ _).trans (blueprint_adjunction a (T.pullback b) g)

/-- Independent proof of the branch blueprint, also allowing different codomains. -/
theorem branch_adjunction {α β₁ β₂ : Type*}
    [HeytingAlgebra α] [HeytingAlgebra β₁] [HeytingAlgebra β₂]
    (T₁ : CFGTransfer α β₁) (T₂ : CFGTransfer α β₂)
    (a : α) (b₁ : β₁) (b₂ : β₂) (g : α) :
    T₁.post (a ⊓ g) ≤ b₁ ∧ T₂.post (a ⊓ g) ≤ b₂ ↔
      g ≤ synthesizeEdgeGuard T₁ a b₁ ⊓ synthesizeEdgeGuard T₂ a b₂ := by
  rw [edge_adjunction, edge_adjunction, le_inf_iff]

/-- Exhaustive soundness on both nonidentity transfers. -/
theorem finite_edge_sound (first : Bool) (a b : State) :
    (keepCoordinate first).post (a ⊓ synthesizeEdgeGuard (keepCoordinate first) a b) ≤ b := by
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  cases first <;> cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> decide

/-- Exhaustive optimality, including the triples where validity is false. -/
theorem finite_edge_weakest (first : Bool) (a b g : State)
    (h : (keepCoordinate first).post (a ⊓ g) ≤ b) :
    g ≤ synthesizeEdgeGuard (keepCoordinate first) a b := by
  revert h
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  rcases g with ⟨g₁, g₂⟩
  cases first <;> cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
    cases g₁ <;> cases g₂ <;> decide

/-- All 256 state/target/target/guard quadruples for independent branches. -/
theorem finite_branch_iff (a b₁ b₂ g : State) :
    (keepCoordinate true).post (a ⊓ g) ≤ b₁ ∧
      (keepCoordinate false).post (a ⊓ g) ≤ b₂ ↔
    g ≤ synthesizeEdgeGuard (keepCoordinate true) a b₁ ⊓
      synthesizeEdgeGuard (keepCoordinate false) a b₂ := by
  rcases a with ⟨a₁, a₂⟩
  rcases b₁ with ⟨b₁₁, b₁₂⟩
  rcases b₂ with ⟨b₂₁, b₂₂⟩
  rcases g with ⟨g₁, g₂⟩
  cases a₁ <;> cases a₂ <;> cases b₁₁ <;> cases b₁₂ <;>
    cases b₂₁ <;> cases b₂₂ <;> cases g₁ <;> cases g₂ <;> decide

/-- A compact truth table for every input to each edge synthesizer. -/
theorem edge_truth_table (first a₁ a₂ b₁ b₂ : Bool) :
    synthesizeEdgeGuard (keepCoordinate first) (a₁, a₂) (b₁, b₂) =
      if first then ((!a₁ || b₁), true) else (true, (!a₂ || b₂)) := by
  cases first <;> cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;> decide

/-- For the full source state, all four branch target combinations give the
corresponding pair of guard bits; neither branch may be discarded. -/
theorem branch_truth_table (b₁ b₂ : Bool) :
    synthesizeEdgeGuard (keepCoordinate true) (true, true) (b₁, false) ⊓
      synthesizeEdgeGuard (keepCoordinate false) (true, true) (false, b₂) =
      (b₁, b₂) := by
  cases b₁ <;> cases b₂ <;> decide

/-- An active source and guard produce a nonbottom postcondition. -/
theorem edge_active_witness :
    (keepCoordinate true).post ((true, true) ⊓ (true, false)) = (true, false) ∧
    (keepCoordinate true).post ((true, true) ⊓ (true, false)) ≤ (true, false) ∧
    (true, false) ≤ synthesizeEdgeGuard (keepCoordinate true) (true, true) (true, false) := by
  decide

/-- A false target admits a nonbottom guard, but rejects the unrestricted guard. -/
theorem edge_restrictive_witness :
    synthesizeEdgeGuard (keepCoordinate true) (true, true) (false, false) = (false, true) ∧
    (keepCoordinate true).post ((true, true) ⊓ (false, true)) ≤ (false, false) ∧
    ¬ ((keepCoordinate true).post ((true, true) ⊓ (true, true)) ≤ (false, false)) ∧
    ¬ ((true, true) ≤ synthesizeEdgeGuard (keepCoordinate true) (true, true) (false, false)) := by
  decide

/-- Both branch premises hold with a nonbottom guard, which equals their synthesis. -/
theorem branch_active_witness :
    (keepCoordinate true).post ((true, true) ⊓ (true, false)) ≤ (true, false) ∧
    (keepCoordinate false).post ((true, true) ⊓ (true, false)) ≤ (false, false) ∧
    synthesizeEdgeGuard (keepCoordinate true) (true, true) (true, false) ⊓
      synthesizeEdgeGuard (keepCoordinate false) (true, true) (false, false) = (true, false) := by
  decide

/-- Each branch can fail while the other succeeds: both conjuncts matter. -/
theorem branches_independent :
    (¬ ((keepCoordinate true).post ((true, true) ⊓ (true, false)) ≤ (false, false)) ∧
      (keepCoordinate false).post ((true, true) ⊓ (true, false)) ≤ (false, false)) ∧
    ((keepCoordinate true).post ((true, true) ⊓ (false, true)) ≤ (false, false) ∧
      ¬ ((keepCoordinate false).post ((true, true) ⊓ (false, true)) ≤ (false, false))) := by
  decide

end Round2

/-!
## Round 3: sequential paths and diamond joins

The four new theorem statements match the blueprint exactly. `CFGTransfer.id`
has identity maps. `T₁.comp T₂` runs `T₁` then `T₂` forward, and pulls targets
back through `T₂` then `T₁`. The composition guard equality is definitional:
its intermediate target is `T₂.pullback c`, with no intermediate state parameter.
Right adjoints preserve meets; both pullback and fixed-state guard synthesis
are right adjoints. Diamond joins use the join of post-states and the meet
of path guards. This is a merge of alternative paths, not a claim that the
paths commute or yield equal post-states.

The audit independently proves all four general claims and checks identity
and associativity laws. For finite tests, compose a coordinate swap with
`Round2.keepCoordinate true` in both orders. Both stages and both resulting
paths are nonidentity; the resulting maps are also nonconstant. An explicit
witness distinguishes the two orders on posts, pullbacks, and guards.
Exhaustive checks cover 32 pullback-meet cases, 32 guard-composition cases,
128 guard-meet cases, and 64 diamond cases. Positive and negative witnesses
also detect replacing the joined post-state by a meet or the guard meet by
a join. No proof invokes a placeholder target theorem.
-/

namespace Round3

open Round2

/-- Identity transfer synthesis is ordinary local synthesis. -/
theorem identity_guard {α : Type*} [HeytingAlgebra α] (a b : α) :
    synthesizeEdgeGuard (CFGTransfer.id α) a b = synthesizeGuard a b := by
  rfl

/-- The identity is neutral on the source side of composition. -/
theorem identity_left {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) : (CFGTransfer.id α).comp T = T := by
  cases T
  rfl

/-- The identity is neutral on the target side of composition. -/
theorem identity_right {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) : T.comp (CFGTransfer.id β) = T := by
  cases T
  rfl

/-- Sequential composition is associative, including the adjunction proof field. -/
theorem composition_assoc {α β γ δ : Type*}
    [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ] [HeytingAlgebra δ]
    (T₁ : CFGTransfer α β) (T₂ : CFGTransfer β γ) (T₃ : CFGTransfer γ δ) :
    (T₁.comp T₂).comp T₃ = T₁.comp (T₂.comp T₃) := by
  rfl

/-- Independent check of the general pullback-meet blueprint. -/
theorem pullback_meet {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (b₁ b₂ : β) :
    T.pullback (b₁ ⊓ b₂) = T.pullback b₁ ⊓ T.pullback b₂ := by
  apply le_antisymm
  · exact le_inf (T.gc.monotone_u inf_le_left) (T.gc.monotone_u inf_le_right)
  · apply (T.gc _ _).mp
    exact le_inf ((T.gc _ _).mpr inf_le_left) ((T.gc _ _).mpr inf_le_right)

/-- Independent check of the general composition blueprint. -/
theorem edge_comp {α β γ : Type*}
    [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ]
    (T₁ : CFGTransfer α β) (T₂ : CFGTransfer β γ) (a : α) (c : γ) :
    synthesizeEdgeGuard (T₁.comp T₂) a c = synthesizeEdgeGuard T₁ a (T₂.pullback c) := by
  rfl

/-- Independent check of the general conjunctive-target blueprint. -/
theorem edge_meet {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (a : α) (b₁ b₂ : β) :
    synthesizeEdgeGuard T a (b₁ ⊓ b₂) =
      synthesizeEdgeGuard T a b₁ ⊓ synthesizeEdgeGuard T a b₂ := by
  unfold synthesizeEdgeGuard synthesizeGuard
  rw [pullback_meet, himp_inf_distrib]

/-- Independent check of the general diamond blueprint, without path equality. -/
theorem diamond_adjunction {α γ : Type*} [HeytingAlgebra α] [HeytingAlgebra γ]
    (P₁ P₂ : CFGTransfer α γ) (a : α) (c : γ) (g : α) :
    P₁.post (a ⊓ g) ⊔ P₂.post (a ⊓ g) ≤ c ↔
      g ≤ synthesizeEdgeGuard P₁ a c ⊓ synthesizeEdgeGuard P₂ a c := by
  exact sup_le_iff.trans (Round2.branch_adjunction P₁ P₂ a c c g)

/-- A nonidentity automorphism, adjoint to itself. -/
def swap : CFGTransfer State State where
  post x := (x.2, x.1)
  pullback b := (b.2, b.1)
  gc := by
    rintro ⟨x₁, x₂⟩ ⟨b₁, b₂⟩
    cases x₁ <;> cases x₂ <;> cases b₁ <;> cases b₂ <;> decide

/-- Both stages are nonidentity; changing their order changes the path. -/
def path (swapFirst : Bool) : CFGTransfer State State :=
  if swapFirst then swap.comp (keepCoordinate true) else (keepCoordinate true).comp swap

/-- Neither map of either composed path is the identity. -/
theorem path_nonidentity (swapFirst : Bool) :
    (path swapFirst).post ≠ id ∧ (path swapFirst).pullback ≠ id := by
  constructor
  · intro h
    have hf := congrFun h (true, true)
    cases swapFirst <;> cases hf
  · intro h
    have hf := congrFun h (false, false)
    cases swapFirst <;> cases hf

/-- Neither composed map degenerates to a constant. -/
theorem path_nonconstant (swapFirst : Bool) :
    (path swapFirst).post (false, false) ≠ (path swapFirst).post (true, true) ∧
    (path swapFirst).pullback (false, false) ≠ (path swapFirst).pullback (true, true) := by
  cases swapFirst <;> decide

/-- Complete truth tables for forward and backward traversal of both paths. -/
theorem path_truth_table (swapFirst x₁ x₂ b₁ b₂ : Bool) :
    (path swapFirst).post (x₁, x₂) =
      (if swapFirst then (x₂, false) else (false, x₁)) ∧
    (path swapFirst).pullback (b₁, b₂) =
      (if swapFirst then (true, b₁) else (b₂, true)) := by
  cases swapFirst <;> cases x₁ <;> cases x₂ <;> cases b₁ <;> cases b₂ <;> decide

/-- Reversing composition changes all three observable operations. -/
theorem composition_order_witness :
    (path true).post (true, false) ≠ (path false).post (true, false) ∧
    (path true).pullback (true, false) ≠ (path false).pullback (true, false) ∧
    synthesizeEdgeGuard (path true) (true, true) (true, false) ≠
      synthesizeEdgeGuard (path false) (true, true) (true, false) := by
  decide

/-- All 32 path/target/target combinations for pullback meet preservation. -/
theorem finite_pullback_meet (swapFirst : Bool) (b c : State) :
    (path swapFirst).pullback (b ⊓ c) =
      (path swapFirst).pullback b ⊓ (path swapFirst).pullback c := by
  rcases b with ⟨b₁, b₂⟩
  rcases c with ⟨c₁, c₂⟩
  cases swapFirst <;> cases b₁ <;> cases b₂ <;> cases c₁ <;> cases c₂ <;> decide

/-- All 32 path/state/target combinations, checked against the intermediate pullback. -/
theorem finite_edge_comp (swapFirst : Bool) (a c : State) :
    synthesizeEdgeGuard (path swapFirst) a c =
      if swapFirst then synthesizeEdgeGuard swap a ((keepCoordinate true).pullback c)
      else synthesizeEdgeGuard (keepCoordinate true) a (swap.pullback c) := by
  rcases a with ⟨a₁, a₂⟩
  rcases c with ⟨c₁, c₂⟩
  cases swapFirst <;> cases a₁ <;> cases a₂ <;> cases c₁ <;> cases c₂ <;> decide

/-- All 128 path/state/target/target combinations for guard meet preservation. -/
theorem finite_edge_meet (swapFirst : Bool) (a b c : State) :
    synthesizeEdgeGuard (path swapFirst) a (b ⊓ c) =
      synthesizeEdgeGuard (path swapFirst) a b ⊓ synthesizeEdgeGuard (path swapFirst) a c := by
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  rcases c with ⟨c₁, c₂⟩
  cases swapFirst <;> cases a₁ <;> cases a₂ <;> cases b₁ <;> cases b₂ <;>
    cases c₁ <;> cases c₂ <;> decide

/-- All 64 state/target/guard combinations for the two composed diamond paths. -/
theorem finite_diamond_iff (a c g : State) :
    (path true).post (a ⊓ g) ⊔ (path false).post (a ⊓ g) ≤ c ↔
      g ≤ synthesizeEdgeGuard (path true) a c ⊓ synthesizeEdgeGuard (path false) a c := by
  rcases a with ⟨a₁, a₂⟩
  rcases c with ⟨c₁, c₂⟩
  rcases g with ⟨g₁, g₂⟩
  cases a₁ <;> cases a₂ <;> cases c₁ <;> cases c₂ <;> cases g₁ <;> cases g₂ <;> decide

/-- Explicit Boolean formulas for both sides' computed states and guards. -/
theorem diamond_truth_table (a₁ a₂ c₁ c₂ g₁ g₂ : Bool) :
    (path true).post ((a₁, a₂) ⊓ (g₁, g₂)) ⊔
      (path false).post ((a₁, a₂) ⊓ (g₁, g₂)) = (a₂ && g₂, a₁ && g₁) ∧
    synthesizeEdgeGuard (path true) (a₁, a₂) (c₁, c₂) ⊓
      synthesizeEdgeGuard (path false) (a₁, a₂) (c₁, c₂) = (!a₁ || c₂, !a₂ || c₁) := by
  cases a₁ <;> cases a₂ <;> cases c₁ <;> cases c₂ <;> cases g₁ <;> cases g₂ <;> decide

/-- An active source and nonbottom guard establish a proper, nonbottom join target. -/
theorem diamond_active_witness :
    (path true).post ((true, true) ⊓ (false, true)) ⊔
      (path false).post ((true, true) ⊓ (false, true)) = (true, false) ∧
    (false, true) ≤ synthesizeEdgeGuard (path true) (true, true) (true, false) ⊓
      synthesizeEdgeGuard (path false) (true, true) (true, false) := by
  decide

/-- Each path can violate the common target while the other path satisfies it. -/
theorem diamond_paths_independent :
    (¬ ((path true).post (false, true) ≤ (false, false)) ∧
      (path false).post (false, true) ≤ (false, false)) ∧
    ((path true).post (true, false) ≤ (false, false) ∧
      ¬ ((path false).post (true, false) ≤ (false, false))) := by
  decide

/-- The false target rejects the unrestricted guard. Swapping either lattice
operation would incorrectly accept this same case. -/
theorem diamond_operator_counterexamples :
    ¬ ((path true).post (true, true) ⊔ (path false).post (true, true) ≤ (false, false)) ∧
    ¬ ((true, true) ≤ synthesizeEdgeGuard (path true) (true, true) (false, false) ⊓
      synthesizeEdgeGuard (path false) (true, true) (false, false)) ∧
    ((path true).post (true, true) ⊓ (path false).post (true, true) ≤ (false, false)) ∧
    ((true, true) ≤ synthesizeEdgeGuard (path true) (true, true) (false, false) ⊔
      synthesizeEdgeGuard (path false) (true, true) (false, false)) := by
  decide

end Round3

/-!
## Round 4: loop preservation and one-step guards

Both definitions and all four new theorem statements match the blueprint.
`IsLoopInvariant L inv` is the preservation condition `L.post inv ≤ inv`;
the adjunction gives exactly `inv ≤ L.pullback inv`. The loop-step guard is
`inv ⇨ L.pullback inv`, which equals top exactly when preservation holds.
Soundness does not assume that the candidate is already invariant. Closure
under meet requires both candidates to be invariant and follows even from
monotonicity of `post`; it does not require `post` to preserve meets.

Scope: preservation alone does not establish an initial state, termination,
or Kripke-Joyal forcing semantics. One-step soundness restores `inv`, not
necessarily `inv ⊓ guard`. The cycle counterexample below shows that an
initial guard check alone need not keep later unguarded iterations in `inv`.

The two nonidentity, nonconstant loops use the eight-element algebra Bool³.
The growth loop has post `(x, x || y, z)` and pullback `(x && y, y, z)`.
The cycle loop has post `(z, x, y)` and inverse pullback `(y, z, x)`.
Each of the first three targets is checked on all 16 loop/candidate choices;
meet closure is checked on all 128 loop/candidate/candidate choices. The
explicit meet witness uses distinct proper invariants with a nonbottom meet.
All proofs are independent of the target placeholders.
-/

namespace Round4

/-- Independent proof of forward/backward loop stability. -/
theorem invariant_pullback {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv : α) :
    IsLoopInvariant L inv ↔ inv ≤ L.pullback inv := by
  exact L.gc inv inv

/-- Independent proof of the unrestricted-guard characterization. -/
theorem invariant_guard_top {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv : α) :
    IsLoopInvariant L inv ↔ synthesizeLoopStepGuard L inv = ⊤ := by
  exact (L.gc inv inv).trans himp_eq_top_iff.symm

/-- Independent soundness proof for every candidate, including non-invariants. -/
theorem loop_sound {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv : α) :
    L.post (inv ⊓ synthesizeLoopStepGuard L inv) ≤ inv := by
  exact (L.gc _ _).mpr (le_himp_iff'.mp le_rfl)

/-- Independent meet-closure proof using monotonicity of the forward map. -/
theorem invariant_meet {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv₁ inv₂ : α) :
    IsLoopInvariant L inv₁ → IsLoopInvariant L inv₂ →
      IsLoopInvariant L (inv₁ ⊓ inv₂) := by
  intro h₁ h₂
  exact le_inf ((L.gc.monotone_l inf_le_left).trans h₁)
    ((L.gc.monotone_l inf_le_right).trans h₂)

/-- Also check the definition's claim that the synthesized one-step guard is weakest. -/
theorem loop_guard_adjunction {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv g : α) :
    L.post (inv ⊓ g) ≤ inv ↔ g ≤ synthesizeLoopStepGuard L inv := by
  exact Round2.edge_adjunction L inv inv g

/-- Three independent Boolean coordinates give nontrivial partial repairs. -/
abbrev State := Bool × Bool × Bool

/-- `true` selects the cycle loop; `false` selects the growth loop. -/
def loop (cycle : Bool) : CFGTransfer State State where
  post x := if cycle then (x.2.2, x.1, x.2.1) else (x.1, x.1 || x.2.1, x.2.2)
  pullback b := if cycle then (b.2.1, b.2.2, b.1) else (b.1 && b.2.1, b.2.1, b.2.2)
  gc := by
    rintro ⟨x₁, x₂, x₃⟩ ⟨b₁, b₂, b₃⟩
    cases cycle <;> cases x₁ <;> cases x₂ <;> cases x₃ <;>
      cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

/-- Both loop maps differ from the identity at the same concrete input. -/
theorem loop_nonidentity (cycle : Bool) :
    (loop cycle).post (true, false, false) ≠ (true, false, false) ∧
    (loop cycle).pullback (true, false, false) ≠ (true, false, false) := by
  cases cycle <;> decide

/-- Neither forward nor backward loop map collapses to a constant. -/
theorem loop_nonconstant (cycle : Bool) :
    (loop cycle).post (false, false, false) ≠ (loop cycle).post (true, true, true) ∧
    (loop cycle).pullback (false, false, false) ≠ (loop cycle).pullback (true, true, true) := by
  cases cycle <;> decide

/-- Exhaustive forward/backward stability check on both loops. -/
theorem finite_invariant_pullback (cycle : Bool) (inv : State) :
    IsLoopInvariant (loop cycle) inv ↔ inv ≤ (loop cycle).pullback inv := by
  unfold IsLoopInvariant
  rcases inv with ⟨x, y, z⟩
  cases cycle <;> cases x <;> cases y <;> cases z <;> decide

/-- Exhaustive check of both directions, including non-invariant candidates. -/
theorem finite_guard_top (cycle : Bool) (inv : State) :
    IsLoopInvariant (loop cycle) inv ↔ synthesizeLoopStepGuard (loop cycle) inv = ⊤ := by
  unfold IsLoopInvariant
  rcases inv with ⟨x, y, z⟩
  cases cycle <;> cases x <;> cases y <;> cases z <;> decide

/-- Exhaustive one-step soundness, without assuming invariance. -/
theorem finite_loop_sound (cycle : Bool) (inv : State) :
    (loop cycle).post (inv ⊓ synthesizeLoopStepGuard (loop cycle) inv) ≤ inv := by
  rcases inv with ⟨x, y, z⟩
  cases cycle <;> cases x <;> cases y <;> cases z <;> decide

/-- Exhaustive meet closure, preserving both premises of the target. -/
theorem finite_invariant_meet (cycle : Bool) (inv₁ inv₂ : State) :
    IsLoopInvariant (loop cycle) inv₁ → IsLoopInvariant (loop cycle) inv₂ →
      IsLoopInvariant (loop cycle) (inv₁ ⊓ inv₂) := by
  unfold IsLoopInvariant
  rcases inv₁ with ⟨x₁, y₁, z₁⟩
  rcases inv₂ with ⟨x₂, y₂, z₂⟩
  cases cycle <;> cases x₁ <;> cases y₁ <;> cases z₁ <;>
    cases x₂ <;> cases y₂ <;> cases z₂ <;> decide

/-- Complete classification: the cycle fixes equal bits; growth requires x ≤ y. -/
theorem invariant_truth_table (cycle x y z : Bool) :
    IsLoopInvariant (loop cycle) (x, y, z) ↔
      if cycle then x = y ∧ y = z else x ≤ y := by
  unfold IsLoopInvariant
  cases cycle <;> cases x <;> cases y <;> cases z <;> decide

/-- Complete loop-step guard table on all candidates. -/
theorem guard_truth_table (cycle x y z : Bool) :
    synthesizeLoopStepGuard (loop cycle) (x, y, z) =
      if cycle then (!x || y, !y || z, !z || x) else (!x || y, true, true) := by
  cases cycle <;> cases x <;> cases y <;> cases z <;> decide

/-- Distinct proper growth invariants have a proper, nonbottom invariant meet. -/
theorem growth_meet_witness :
    IsLoopInvariant (loop false) (true, true, false) ∧
    IsLoopInvariant (loop false) (false, true, true) ∧
    ((true, true, false) ⊓ (false, true, true) : State) = (false, true, false) ∧
    IsLoopInvariant (loop false) (false, true, false) := by
  unfold IsLoopInvariant
  decide

/-- The guard repairs a genuine failure while retaining a nonbottom state. -/
theorem growth_repair_witness :
    ¬ IsLoopInvariant (loop false) (true, false, true) ∧
    synthesizeLoopStepGuard (loop false) (true, false, true) = (false, true, true) ∧
    (true, false, true) ⊓ synthesizeLoopStepGuard (loop false) (true, false, true) =
      (false, false, true) ∧
    (loop false).post (false, false, true) = (false, false, true) := by
  unfold IsLoopInvariant
  decide

/-- Either missing invariance premise can make the conjunction non-invariant. -/
theorem meet_requires_both_premises :
    IsLoopInvariant (loop false) (true, true, true) ∧
    ¬ IsLoopInvariant (loop false) (true, false, true) ∧
    ¬ IsLoopInvariant (loop false) ((true, true, true) ⊓ (true, false, true)) ∧
    ¬ IsLoopInvariant (loop false) ((true, false, true) ⊓ (true, true, true)) := by
  unfold IsLoopInvariant
  decide

/-- The cycle guard is restrictive and leaves a nonbottom starting state. -/
theorem cycle_repair_witness :
    ¬ IsLoopInvariant (loop true) (true, true, false) ∧
    synthesizeLoopStepGuard (loop true) (true, true, false) = (true, false, true) ∧
    (true, true, false) ⊓ synthesizeLoopStepGuard (loop true) (true, true, false) =
      (true, false, false) := by
  unfold IsLoopInvariant
  decide

/-- Restoring inv once does not ensure the guard persists or allow another
unguarded step. This refutes a stronger interpretation, not the target. -/
theorem one_step_not_persistent :
    let L := loop true
    let inv : State := (true, true, false)
    let guarded := inv ⊓ synthesizeLoopStepGuard L inv
    L.post guarded ≤ inv ∧ ¬ IsLoopInvariant L guarded ∧
      ¬ (L.post (L.post guarded) ≤ inv) := by
  dsimp only
  unfold IsLoopInvariant
  decide

/-- Invariance requires a forward inclusion, not equality with the post-state. -/
theorem invariance_need_not_be_fixedpoint :
    IsLoopInvariant (Round2.keepCoordinate true) (false, true) ∧
    (Round2.keepCoordinate true).post (false, true) ≠ (false, true) := by
  unfold IsLoopInvariant
  decide

end Round4

/-!
## Round 5: inductive witnesses and preheader hoisting

Both definitions and all four new statements match the blueprint exactly.
`IsInductiveFor L inv target` contains preservation and `inv ≤ target`.
`hoistLoopGuard E a₀ inv` establishes the chosen invariant on loop entry;
it does not synthesize that invariant or minimize the guard over all possible
invariants. Entry-target soundness needs only the entailment conjunct, while
the one-step target theorem needs both. Two-step preservation follows from
monotonicity and invariance. No termination or unrestricted iteration theorem
is part of these four statements.

The preheader has two Boolean coordinates, and the loop header has three:
`E.post (x,y) = (y,false,x)` and `E.pullback (u,v,w) = (w,u)`.
Both maps are nonconstant. With the growth loop from Round 4, preheader 11
and invariant/target 110 produce guard 01, entry 100, and loop state 110.
Thus the guard is restrictive, execution remains nonempty, and the loop
actually changes the entered state. Tests also reject missing preservation,
missing target entailment, and omitting the entry guard.

Exhaustive checks cover 16 loop/candidate cases for two-step preservation,
512 loop/preheader/invariant/target cases for each target theorem, and 64
loop/preheader/invariant cases for step-invariance: 1104 cases in total.
All audit declarations, including previous rounds, are checked without
`sorryAx` or `Classical.choice`; only `propext` and `Quot.sound` may remain.
-/

namespace Round5

/-- Independent proof of preservation across two composed loop iterations. -/
theorem iterate_two {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv : α) (h : IsLoopInvariant L inv) :
    (L.comp L).post inv ≤ inv := by
  exact (L.gc.monotone_l h).trans h

/-- Hoisting establishes the selected invariant without assuming preservation. -/
theorem entry_invariant {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (a₀ : α) (inv : β) :
    E.post (a₀ ⊓ hoistLoopGuard E a₀ inv) ≤ inv := by
  exact (E.gc _ _).mpr (le_himp_iff'.mp le_rfl)

/-- Independent proof of the entry-target blueprint. -/
theorem entry_target {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    E.post (a₀ ⊓ hoistLoopGuard E a₀ inv) ≤ target := by
  exact (entry_invariant E a₀ inv).trans h.2

/-- Independent proof of the preheader-plus-loop preservation blueprint. -/
theorem step_invariant {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv : β) (h : IsLoopInvariant L inv) :
    L.post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ inv := by
  exact (L.gc.monotone_l (entry_invariant E a₀ inv)).trans h

/-- Independent proof of the preheader-plus-loop target blueprint. -/
theorem step_target {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    L.post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ target := by
  exact (step_invariant E L a₀ inv h.1).trans h.2

/-- Check the definition's weakest-guard claim for the selected invariant. -/
theorem hoist_adjunction {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (a₀ g : α) (inv : β) :
    E.post (a₀ ⊓ g) ≤ inv ↔ g ≤ hoistLoopGuard E a₀ inv := by
  exact Round2.edge_adjunction E a₀ inv g

abbrev PreState := Round2.State
abbrev HeaderState := Round4.State

/-- A nonconstant entry edge between different finite state domains. -/
def entry : CFGTransfer PreState HeaderState where
  post x := (x.2, false, x.1)
  pullback b := (b.2.2, b.1)
  gc := by
    rintro ⟨x₁, x₂⟩ ⟨b₁, b₂, b₃⟩
    cases x₁ <;> cases x₂ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

/-- Neither direction of the entry edge is constant. -/
theorem entry_nonconstant :
    entry.post (false, false) ≠ entry.post (true, true) ∧
    entry.pullback (false, false, false) ≠ entry.pullback (true, true, true) := by
  decide

/-- All 32 preheader/invariant combinations have this Boolean guard formula. -/
theorem hoist_truth_table (a b x y z : Bool) :
    hoistLoopGuard entry (a, b) (x, y, z) = (!a || z, !b || x) := by
  cases a <;> cases b <;> cases x <;> cases y <;> cases z <;> decide

/-- All 16 loop/candidate cases, preserving the invariance premise. -/
theorem finite_iterate_two (cycle : Bool) (inv : HeaderState) :
    IsLoopInvariant (Round4.loop cycle) inv →
      ((Round4.loop cycle).comp (Round4.loop cycle)).post inv ≤ inv := by
  unfold IsLoopInvariant
  rcases inv with ⟨x, y, z⟩
  cases cycle <;> cases x <;> cases y <;> cases z <;> decide

/-- All 512 loop/preheader/invariant/target cases for entry target soundness. -/
theorem finite_entry_target (cycle : Bool) (a₀ : PreState) (inv target : HeaderState) :
    IsInductiveFor (Round4.loop cycle) inv target →
      entry.post (a₀ ⊓ hoistLoopGuard entry a₀ inv) ≤ target := by
  unfold IsInductiveFor IsLoopInvariant
  rcases a₀ with ⟨a₁, a₂⟩
  rcases inv with ⟨i₁, i₂, i₃⟩
  rcases target with ⟨t₁, t₂, t₃⟩
  cases cycle <;> cases a₁ <;> cases a₂ <;> cases i₁ <;> cases i₂ <;>
    cases i₃ <;> cases t₁ <;> cases t₂ <;> cases t₃ <;> decide

/-- All 64 loop/preheader/invariant cases for preservation after entry and a step. -/
theorem finite_step_invariant (cycle : Bool) (a₀ : PreState) (inv : HeaderState) :
    IsLoopInvariant (Round4.loop cycle) inv →
      (Round4.loop cycle).post (entry.post (a₀ ⊓ hoistLoopGuard entry a₀ inv)) ≤ inv := by
  unfold IsLoopInvariant
  rcases a₀ with ⟨a₁, a₂⟩
  rcases inv with ⟨i₁, i₂, i₃⟩
  cases cycle <;> cases a₁ <;> cases a₂ <;> cases i₁ <;> cases i₂ <;> cases i₃ <;> decide

/-- All 512 loop/preheader/invariant/target cases for target soundness after a step. -/
theorem finite_step_target (cycle : Bool) (a₀ : PreState) (inv target : HeaderState) :
    IsInductiveFor (Round4.loop cycle) inv target →
      (Round4.loop cycle).post (entry.post (a₀ ⊓ hoistLoopGuard entry a₀ inv)) ≤ target := by
  unfold IsInductiveFor IsLoopInvariant
  rcases a₀ with ⟨a₁, a₂⟩
  rcases inv with ⟨i₁, i₂, i₃⟩
  rcases target with ⟨t₁, t₂, t₃⟩
  cases cycle <;> cases a₁ <;> cases a₂ <;> cases i₁ <;> cases i₂ <;>
    cases i₃ <;> cases t₁ <;> cases t₂ <;> cases t₃ <;> decide

/-- A proper inductive invariant, restrictive nonbottom guard, and changing loop state. -/
theorem active_hoist_witness :
    let L := Round4.loop false
    let a₀ : PreState := (true, true)
    let inv : HeaderState := (true, true, false)
    let guard := hoistLoopGuard entry a₀ inv
    let entered := entry.post (a₀ ⊓ guard)
    IsInductiveFor L inv inv ∧ guard = (false, true) ∧
      a₀ ⊓ guard = (false, true) ∧ entered = (true, false, false) ∧
      L.post entered = inv ∧ (L.comp L).post entered ≤ inv := by
  dsimp only
  unfold IsInductiveFor IsLoopInvariant
  decide

/-- Entry can establish inv while a subsequent loop step violates it:
preservation is necessary for both loop-step claims and the two-step claim. -/
theorem missing_invariance_counterexample :
    let L := Round4.loop false
    let inv : HeaderState := (true, false, false)
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) inv)
    ¬ IsLoopInvariant L inv ∧ entered = inv ∧
      ¬ ((L.comp L).post inv ≤ inv) ∧ ¬ (L.post entered ≤ inv) := by
  dsimp only
  unfold IsLoopInvariant
  decide

/-- Preservation alone cannot guarantee a target not implied by the invariant. -/
theorem missing_entailment_counterexample :
    let L := Round4.loop false
    let inv : HeaderState := (true, true, false)
    let target : HeaderState := (false, true, false)
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) inv)
    IsLoopInvariant L inv ∧ ¬ (inv ≤ target) ∧
      ¬ (entered ≤ target) ∧ ¬ (L.post entered ≤ target) := by
  dsimp only
  unfold IsLoopInvariant
  decide

/-- Omitting the restrictive guard breaks both entry and post-step target safety. -/
theorem missing_guard_counterexample :
    ¬ (entry.post (true, true) ≤ (true, true, false)) ∧
    ¬ ((Round4.loop false).post (entry.post (true, true)) ≤ (true, true, false)) := by
  decide

/-- Hoisting is weakest for the chosen inv, not necessarily for the target:
a larger guard can still establish a larger proper target. -/
theorem target_guard_can_be_weaker :
    let L := Round4.loop false
    let inv : HeaderState := (false, true, false)
    let target : HeaderState := (true, true, false)
    let g : PreState := (false, true)
    IsInductiveFor L inv target ∧ entry.post g ≤ target ∧
      L.post (entry.post g) ≤ target ∧
      ¬ (g ≤ hoistLoopGuard entry (true, true) inv) := by
  dsimp only
  unfold IsInductiveFor IsLoopInvariant
  decide

end Round5

/-!
## Round 6: arbitrary finite iteration

`CFGTransfer.iterate` starts at identity and appends one loop step in its
successor clause. Thus the forward map is `L.post ∘ post_n`, while the
pullback is `pullback_n ∘ L.pullback`. All four new statements match the
blueprint, including `n = 0`. In the hoisted claims, zero counts loop steps
only: the entry edge has already run. Induction proves safety for every
finite iteration count; this does not prove termination or a full forcing
semantics. The same preheader guard is used once, with no repeated guard
test in the iterated transfer.

The general proofs below cover every natural number independently of the
target placeholders. Separate computation checks use all depths 0 through
5, the three-coordinate cycle, and a shift loop whose post is `(false,x,y)`
and whose pullback is `(v,w,true)`. These cover 96 forward-invariance cases,
96 pullback cases, 384 hoisted-invariance cases, and 3072 hoisted-target
cases: 3648 bounded checks, in addition to the unbounded induction proofs.
Exact traces detect off-by-one errors and distinguish forward traversal
from pullback. A delayed-failure witness passes at entry and after one
step, fails after two, and passes again after three, showing why shallow
checks cannot substitute for an inductive invariant.
-/

namespace Round6

/-- Zero iterations are exactly the identity transfer. -/
theorem iterate_zero {α : Type*} [HeytingAlgebra α] (L : CFGTransfer α α) :
    L.iterate 0 = CFGTransfer.id α := by
  rfl

/-- One iteration is exactly the original transfer, including its proof field. -/
theorem iterate_one {α : Type*} [HeytingAlgebra α] (L : CFGTransfer α α) :
    L.iterate 1 = L := by
  cases L
  rfl

/-- Successor iteration runs the loop last forward and first backward. -/
theorem successor_maps {α : Type*} [HeytingAlgebra α] (L : CFGTransfer α α) (n : ℕ) :
    (L.iterate (n + 1)).post = L.post ∘ (L.iterate n).post ∧
    (L.iterate (n + 1)).pullback = (L.iterate n).pullback ∘ L.pullback := by
  exact ⟨rfl, rfl⟩

/-- Independent induction proof of the arbitrary-iteration invariant target. -/
theorem iterate_invariant {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv : α) (h : IsLoopInvariant L inv) :
    ∀ n : ℕ, (L.iterate n).post inv ≤ inv := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (L.gc.monotone_l ih).trans h

/-- Independent pullback stability proof for all iteration counts. -/
theorem iterate_pullback {α : Type*} [HeytingAlgebra α]
    (L : CFGTransfer α α) (inv : α) (h : IsLoopInvariant L inv) :
    ∀ n : ℕ, inv ≤ (L.iterate n).pullback inv := by
  intro n
  exact ((L.iterate n).gc _ _).mp (iterate_invariant L inv h n)

/-- Establish inv at entry, then preserve it for any finite number of steps. -/
theorem hoist_invariant {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv : β) (h : IsLoopInvariant L inv) :
    ∀ n : ℕ, (L.iterate n).post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ inv := by
  intro n
  exact ((L.iterate n).gc.monotone_l (Round5.entry_invariant E a₀ inv)).trans
    (iterate_invariant L inv h n)

/-- Independent target-safety proof for all iteration counts. -/
theorem hoist_target {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    ∀ n : ℕ, (L.iterate n).post (E.post (a₀ ⊓ hoistLoopGuard E a₀ inv)) ≤ target := by
  intro n
  exact (hoist_invariant E L a₀ inv h.1 n).trans h.2

open Round5

/-- A shift with observable behavior at zero, one, two, and three steps. -/
def shift : CFGTransfer HeaderState HeaderState where
  post x := (false, x.1, x.2.1)
  pullback b := (b.2.1, b.2.2, true)
  gc := by
    rintro ⟨x₁, x₂, x₃⟩ ⟨b₁, b₂, b₃⟩
    cases x₁ <;> cases x₂ <;> cases x₃ <;>
      cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

/-- Select the existing cycle or the new shift, both nonidentity and nonconstant. -/
def loop (cyclic : Bool) : CFGTransfer HeaderState HeaderState :=
  if cyclic then Round4.loop true else shift

/-- Six concrete depths; this bounded predicate does not stand for all naturals. -/
def ThroughFive (P : ℕ → Prop) : Prop := P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5

/-- Exhaustive forward preservation for both loops, all candidates, and six depths. -/
theorem finite_iterate (cyclic : Bool) (inv : HeaderState) :
    IsLoopInvariant (loop cyclic) inv →
      ThroughFive (fun n => ((loop cyclic).iterate n).post inv ≤ inv) := by
  unfold IsLoopInvariant ThroughFive
  rcases inv with ⟨x, y, z⟩
  cases cyclic <;> cases x <;> cases y <;> cases z <;> decide

/-- Exhaustive backward preservation at the same six depths. -/
theorem finite_pullback (cyclic : Bool) (inv : HeaderState) :
    IsLoopInvariant (loop cyclic) inv →
      ThroughFive (fun n => inv ≤ ((loop cyclic).iterate n).pullback inv) := by
  unfold IsLoopInvariant ThroughFive
  rcases inv with ⟨x, y, z⟩
  cases cyclic <;> cases x <;> cases y <;> cases z <;> decide

/-- Exhaustive hoisted preservation, retaining every premise. -/
theorem finite_hoist_invariant (cyclic : Bool) (a₀ : PreState) (inv : HeaderState) :
    IsLoopInvariant (loop cyclic) inv →
      ThroughFive (fun n =>
        ((loop cyclic).iterate n).post (entry.post (a₀ ⊓ hoistLoopGuard entry a₀ inv)) ≤ inv) := by
  unfold IsLoopInvariant ThroughFive
  rcases a₀ with ⟨a₁, a₂⟩
  rcases inv with ⟨i₁, i₂, i₃⟩
  cases cyclic <;> cases a₁ <;> cases a₂ <;> cases i₁ <;> cases i₂ <;> cases i₃ <;> decide

/-- Exhaustive hoisted target safety, varying the target independently of inv. -/
theorem finite_hoist_target (cyclic : Bool) (a₀ : PreState) (inv target : HeaderState) :
    IsInductiveFor (loop cyclic) inv target →
      ThroughFive (fun n =>
        ((loop cyclic).iterate n).post (entry.post (a₀ ⊓ hoistLoopGuard entry a₀ inv)) ≤ target) := by
  unfold IsInductiveFor IsLoopInvariant ThroughFive
  rcases a₀ with ⟨a₁, a₂⟩
  rcases inv with ⟨i₁, i₂, i₃⟩
  rcases target with ⟨t₁, t₂, t₃⟩
  cases cyclic <;> cases a₁ <;> cases a₂ <;> cases i₁ <;> cases i₂ <;>
    cases i₃ <;> cases t₁ <;> cases t₂ <;> cases t₃ <;> decide

/-- All input states exhibit the expected shift and its backward adjoint. -/
theorem shift_trace (x y z : Bool) :
    (shift.iterate 0).post (x, y, z) = (x, y, z) ∧
    (shift.iterate 1).post (x, y, z) = (false, x, y) ∧
    (shift.iterate 2).post (x, y, z) = (false, false, x) ∧
    (shift.iterate 3).post (x, y, z) = (false, false, false) ∧
    (shift.iterate 5).post (x, y, z) = (false, false, false) ∧
    (shift.iterate 0).pullback (x, y, z) = (x, y, z) ∧
    (shift.iterate 1).pullback (x, y, z) = (y, z, true) ∧
    (shift.iterate 2).pullback (x, y, z) = (z, true, true) ∧
    (shift.iterate 3).pullback (x, y, z) = (true, true, true) ∧
    (shift.iterate 5).pullback (x, y, z) = (true, true, true) := by
  cases x <;> cases y <;> cases z <;> decide

/-- The cycle has period three; its post and pullback rotate in opposite directions. -/
theorem cycle_trace (x y z : Bool) :
    ((Round4.loop true).iterate 1).post (x, y, z) = (z, x, y) ∧
    ((Round4.loop true).iterate 2).post (x, y, z) = (y, z, x) ∧
    ((Round4.loop true).iterate 3).post (x, y, z) = (x, y, z) ∧
    ((Round4.loop true).iterate 5).post (x, y, z) = (y, z, x) ∧
    ((Round4.loop true).iterate 1).pullback (x, y, z) = (y, z, x) ∧
    ((Round4.loop true).iterate 2).pullback (x, y, z) = (z, x, y) ∧
    ((Round4.loop true).iterate 3).pullback (x, y, z) = (x, y, z) ∧
    ((Round4.loop true).iterate 5).pullback (x, y, z) = (z, x, y) := by
  cases x <;> cases y <;> cases z <;> decide

/-- A proper, nonbottom invariant is preserved by strict decrease, not equality. -/
theorem shift_invariant_witness :
    IsLoopInvariant shift (false, true, true) ∧
    (shift.iterate 1).post (false, true, true) = (false, false, true) ∧
    (shift.iterate 2).post (false, true, true) = (false, false, false) := by
  unfold IsLoopInvariant
  decide

/-- Zero iterations still enter the loop; positive depths use the already established inv. -/
theorem growth_hoisted_trace :
    let L := Round4.loop false
    let inv : HeaderState := (true, true, false)
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) inv)
    (L.iterate 0).post entered = (true, false, false) ∧
    (L.iterate 1).post entered = inv ∧
    (L.iterate 2).post entered = inv ∧ (L.iterate 5).post entered = inv := by
  dsimp only
  decide

/-- Concrete non-vacuity for the full unbounded claim, with no per-step guard check. -/
theorem growth_hoist_all_steps :
    ∀ n : ℕ, ((Round4.loop false).iterate n).post
      (entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) (true, true, false))) ≤
        (true, true, false) := by
  exact hoist_invariant entry (Round4.loop false) (true, true) (true, true, false)
    (by unfold IsLoopInvariant; decide)

/-- Without invariance, entry and one step can pass, while two steps fail.
Success at three steps does not repair the failure of the universal claim. -/
theorem delayed_failure_counterexample :
    let inv : HeaderState := (true, true, false)
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) inv)
    ¬ IsLoopInvariant shift inv ∧
    (shift.iterate 0).post entered ≤ inv ∧ (shift.iterate 1).post entered ≤ inv ∧
    ¬ ((shift.iterate 2).post entered ≤ inv) ∧ (shift.iterate 3).post entered ≤ inv := by
  dsimp only
  unfold IsLoopInvariant
  decide

end Round6

/-!
## Round 7: algebraic forcing and rewrite preconditions

The two definitions and all four theorem statements match the blueprint.
`Forces a p` means `a ≤ p`; `ForcesAfter T a q` means `T.post a ≤ q`.
The first equivalence is the transfer adjunction, and the guard/chain
equivalences follow from Heyting adjunction and meet. The hoisted forcing
claim unfolds to the arbitrary-iteration target claim from Round 6.

Scope: these definitions implement an order-based forcing fragment. They
introduce no site, covers, or recursive quantifier/locality clauses for full
Kripke-Joyal semantics. The rewrite-chain theorem establishes both conditions
at one guarded stage; it does not model sequential state-changing rewrites.
A concrete counterexample below separates these interpretations.

The independent computation checks cover 32 heterogeneous transfer cases,
64 guarded-forcing cases, 256 rewrite-chain cases, and 3072 hoisted forcing
cases at depths 0 through 5: 3424 cases, in addition to the Bool truth table,
direct Prop proofs, and general proofs (including all natural iteration counts).
Nonbottom witnesses and independently failing rewrite conditions rule out
vacuous examples. The entire audit retains zero sorryAx/choice dependencies.
-/

namespace Round7

/-- Independent forcing/pullback equivalence, with the original transfer orientation. -/
theorem after_pullback {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (a : α) (q : β) :
    ForcesAfter T a q ↔ Forces a (T.pullback q) := by
  exact T.gc a q

/-- Independent guarded-forcing equivalence. -/
theorem guard_forcing {α : Type*} [HeytingAlgebra α] (a p g : α) :
    Forces (a ⊓ g) p ↔ Forces g (synthesizeGuard a p) := by
  exact blueprint_adjunction a p g

/-- Independent equivalence for two conditions at the same guarded stage. -/
theorem rewrite_chain {α : Type*} [HeytingAlgebra α] (a p₁ p₂ g : α) :
    Forces (a ⊓ g) (p₁ ⊓ p₂) ↔ Forces g (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂) := by
  unfold Forces synthesizeGuard
  simp only [le_inf_iff, le_himp_iff']

/-- Independent hoisted forcing proof for every natural iteration count. -/
theorem hoisted_forcing {α β : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (L : CFGTransfer β β)
    (a₀ : α) (inv target : β) (h : IsInductiveFor L inv target) :
    ∀ n : ℕ, ForcesAfter (E.comp (L.iterate n)) (a₀ ⊓ hoistLoopGuard E a₀ inv) target := by
  exact Round6.hoist_target E L a₀ inv target h

/-- All four Bool forcing judgments, including the one rejected judgment. -/
theorem bool_forcing_table :
    Forces false false ∧ Forces false true ∧ Forces true true ∧ ¬ Forces true false := by
  unfold Forces
  decide

/-- On Prop, forcing is implication; it is not an assertion of its premise. -/
theorem prop_forcing (a p : Prop) : Forces a p ↔ (a → p) := by
  rfl

/-- Direct constructive Prop proof of the guard claim. -/
theorem prop_guard (a p g : Prop) :
    Forces (a ⊓ g) p ↔ Forces g (synthesizeGuard a p) := by
  change ((a ∧ g) → p) ↔ (g → a → p)
  exact ⟨fun h hg ha => h ⟨ha, hg⟩, fun h hag => h hag.2 hag.1⟩

/-- Direct constructive Prop proof, separately extracting both rewrite conditions. -/
theorem prop_chain (a p₁ p₂ g : Prop) :
    Forces (a ⊓ g) (p₁ ⊓ p₂) ↔ Forces g (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂) := by
  change ((a ∧ g) → p₁ ∧ p₂) ↔ (g → (a → p₁) ∧ (a → p₂))
  constructor
  · exact fun h hg => ⟨fun ha => (h ⟨ha, hg⟩).1, fun ha => (h ⟨ha, hg⟩).2⟩
  · exact fun h hag => ⟨(h hag.2).1 hag.1, (h hag.2).2 hag.1⟩

open Round5

/-- All 32 forcing judgments across the nonconstant Bool²-to-Bool³ entry transfer. -/
theorem finite_after (a : PreState) (q : HeaderState) :
    ForcesAfter entry a q ↔ Forces a (entry.pullback q) := by
  unfold ForcesAfter Forces
  rcases a with ⟨a₁, a₂⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases a₁ <;> cases a₂ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- All 64 two-coordinate guarded-forcing cases. -/
theorem finite_guard (a p g : PreState) :
    Forces (a ⊓ g) p ↔ Forces g (synthesizeGuard a p) := by
  unfold Forces
  rcases a with ⟨a₁, a₂⟩
  rcases p with ⟨p₁, p₂⟩
  rcases g with ⟨g₁, g₂⟩
  cases a₁ <;> cases a₂ <;> cases p₁ <;> cases p₂ <;> cases g₁ <;> cases g₂ <;> decide

/-- All 256 two-coordinate stage/condition/condition/guard combinations. -/
theorem finite_chain (a p₁ p₂ g : PreState) :
    Forces (a ⊓ g) (p₁ ⊓ p₂) ↔ Forces g (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂) := by
  unfold Forces
  rcases a with ⟨a₁, a₂⟩
  rcases p₁ with ⟨p₁₁, p₁₂⟩
  rcases p₂ with ⟨p₂₁, p₂₂⟩
  rcases g with ⟨g₁, g₂⟩
  cases a₁ <;> cases a₂ <;> cases p₁₁ <;> cases p₁₂ <;>
    cases p₂₁ <;> cases p₂₂ <;> cases g₁ <;> cases g₂ <;> decide

/-- Both dynamic loops, all preheaders/invariants/targets, and depths 0 through 5. -/
theorem finite_hoisted_forcing (cyclic : Bool) (a₀ : PreState) (inv target : HeaderState) :
    IsInductiveFor (Round6.loop cyclic) inv target →
      Round6.ThroughFive (fun n =>
        ForcesAfter (entry.comp ((Round6.loop cyclic).iterate n))
          (a₀ ⊓ hoistLoopGuard entry a₀ inv) target) := by
  unfold IsInductiveFor IsLoopInvariant Round6.ThroughFive ForcesAfter Forces
  rcases a₀ with ⟨a₁, a₂⟩
  rcases inv with ⟨i₁, i₂, i₃⟩
  rcases target with ⟨t₁, t₂, t₃⟩
  cases cyclic <;> cases a₁ <;> cases a₂ <;> cases i₁ <;> cases i₂ <;>
    cases i₃ <;> cases t₁ <;> cases t₂ <;> cases t₃ <;> decide

/-- Using post in place of pullback, or ignoring the transfer, changes the answer. -/
theorem transfer_orientation_witness :
    let T := Round4.loop true
    let a : HeaderState := (true, false, false)
    let q : HeaderState := (false, true, false)
    ForcesAfter T a q ∧ Forces a (T.pullback q) ∧
      ¬ Forces a (T.post q) ∧ ¬ Forces a q := by
  dsimp only
  unfold ForcesAfter Forces
  decide

/-- Distinct proper preconditions share a nonbottom satisfying guarded stage. -/
theorem rewrite_active_witness :
    let a : HeaderState := (true, true, true)
    let p₁ : HeaderState := (true, true, false)
    let p₂ : HeaderState := (true, false, true)
    let g : HeaderState := (true, false, false)
    Forces (a ⊓ g) (p₁ ⊓ p₂) ∧
      Forces g (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂) ∧
      ¬ Forces a (p₁ ⊓ p₂) := by
  dsimp only
  unfold Forces
  decide

/-- Each rewrite condition can fail while the other holds. -/
theorem rewrite_conditions_independent :
    (Forces (false, true, false) (true, true, false) ∧
      ¬ Forces (false, true, false) (true, false, true)) ∧
    (¬ Forces (false, false, true) (true, true, false) ∧
      Forces (false, false, true) (true, false, true)) := by
  unfold Forces
  decide

/-- Replacing either meet by join accepts a guard that fails the conjunction. -/
theorem rewrite_join_counterexample :
    let a : HeaderState := (true, true, true)
    let p₁ : HeaderState := (true, true, false)
    let p₂ : HeaderState := (true, false, true)
    let g : HeaderState := (false, true, false)
    Forces g (synthesizeGuard a p₁ ⊔ synthesizeGuard a p₂) ∧
      Forces (a ⊓ g) (p₁ ⊔ p₂) ∧ ¬ Forces (a ⊓ g) (p₁ ⊓ p₂) := by
  dsimp only
  unfold Forces
  decide

/-- The theorem does not promise that a state-changing first rewrite preserves
the second precondition. Both hold initially, but cycling the stage breaks p₂. -/
theorem same_stage_is_not_sequential :
    Forces (true, false, false) ((true, true, false) ⊓ (true, false, true)) ∧
    ¬ ForcesAfter (Round4.loop true) (true, false, false) (true, false, true) := by
  unfold ForcesAfter Forces
  decide

/-- A proper inductive witness succeeds in entry-then-loop order, but not in reverse. -/
theorem hoist_composition_order :
    let E := Round4.loop true
    let L := Round4.loop false
    let inv : HeaderState := (false, true, false)
    let a₀ : HeaderState := (true, true, true)
    let g := hoistLoopGuard E a₀ inv
    IsInductiveFor L inv inv ∧ g = (true, false, false) ∧
    ForcesAfter (E.comp (L.iterate 1)) (a₀ ⊓ g) inv ∧
    ¬ ForcesAfter ((L.iterate 1).comp E) (a₀ ⊓ g) inv := by
  dsimp only
  unfold IsInductiveFor IsLoopInvariant ForcesAfter Forces
  decide

/-- The same nonbottom guarded stage forces the proper target at every depth. -/
theorem hoisted_forcing_all_steps :
    ∀ n : ℕ, ForcesAfter ((Round4.loop true).comp ((Round4.loop false).iterate n))
      ((true, true, true) ⊓
        hoistLoopGuard (Round4.loop true) (true, true, true) (false, true, false))
      (false, true, false) := by
  exact hoisted_forcing (Round4.loop true) (Round4.loop false) (true, true, true)
    (false, true, false) (false, true, false)
    (by unfold IsInductiveFor IsLoopInvariant; decide)

/-- Without inductivity, the forcing claim can pass at depths 0 and 1 but fail at 2. -/
theorem delayed_forcing_failure :
    let inv : HeaderState := (true, true, false)
    let guarded := (true, true) ⊓ hoistLoopGuard entry (true, true) inv
    ¬ IsInductiveFor Round6.shift inv inv ∧
    ForcesAfter (entry.comp (Round6.shift.iterate 0)) guarded inv ∧
    ForcesAfter (entry.comp (Round6.shift.iterate 1)) guarded inv ∧
    ¬ ForcesAfter (entry.comp (Round6.shift.iterate 2)) guarded inv := by
  dsimp only
  unfold IsInductiveFor IsLoopInvariant ForcesAfter Forces
  decide

end Round7

/-!
## Round 8: stage-guarded IR equivalence

The definition and all four theorem statements match the blueprint exactly.
`GuardedEquiv eval p t₁ t₂` checks equality at every `s ≤ p`, not just at `p`.
All guards include bottom, so even a bottom guard requires equality there.
No evaluator monotonicity or restriction law is assumed or needed: both
rewrites are compared at the same stage. Synthesized-chain soundness gives
equality at the guarded stage, not at the original stage, and does not claim
the residual is weakest for endpoint equivalence.

The concrete IR has variables, constants, and binary addition. Its numeric
interpretation uses 0/1 inputs and natural addition; its Boolean interpretation
uses disjunction. The chain is x+(y+z) -> y+z -> z. The first guard forbids x,
the second forbids y, and their meet still permits z. The numeric endpoint
values agree exactly when x=y=false, and vary with z even inside that guard.
Both evaluators have the same exact classification of guarded equivalence;
Boolean pointwise equality alone can hold outside the valid guard.

Besides general proofs, the audit checks every guard for all three pairs,
all 64 pairs of guards for transitivity, and all 512 source/guard/guard
combinations for synthesis, under both evaluators. Explicit witnesses reject
guard joins, omitted premises, equality only at the maximal stage, and
assuming equality at the original unguarded stage. No target placeholder or
choice-dependent proof is used.
-/

namespace Round8

/-- Independent reflexivity proof, requiring no property of the evaluator. -/
theorem equiv_refl {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (t : Term) : GuardedEquiv eval ⊤ t t := by
  intro s _
  rfl

/-- Independent symmetry proof at each forcing stage. -/
theorem equiv_symm {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (p : α) (t₁ t₂ : Term) :
    GuardedEquiv eval p t₁ t₂ → GuardedEquiv eval p t₂ t₁ := by
  intro h s hs
  exact (h s hs).symm

/-- Both rewrite premises apply to every stage below the meet. -/
theorem equiv_trans {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (p₁ p₂ : α) (t₁ t₂ t₃ : Term)
    (h₁ : GuardedEquiv eval p₁ t₁ t₂) (h₂ : GuardedEquiv eval p₂ t₂ t₃) :
    GuardedEquiv eval (p₁ ⊓ p₂) t₁ t₃ := by
  intro s hs
  exact (h₁ s (hs.trans inf_le_left)).trans (h₂ s (hs.trans inf_le_right))

/-- Independent synthesized-chain proof using the audited forcing equivalence. -/
theorem synthesized_chain {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (a p₁ p₂ : α) (t₁ t₂ t₃ : Term)
    (h₁ : GuardedEquiv eval p₁ t₁ t₂) (h₂ : GuardedEquiv eval p₂ t₂ t₃) :
    eval (a ⊓ (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂)) t₁ =
      eval (a ⊓ (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂)) t₃ := by
  exact equiv_trans eval p₁ p₂ t₁ t₂ t₃ h₁ h₂ _
    ((Round7.rewrite_chain a p₁ p₂ _).mpr le_rfl)

abbrev Stage := Round4.State

/-- A small expression IR with two independently removable input contributions. -/
inductive IR where
  | zero
  | one
  | x
  | y
  | z
  | add (left right : IR)

/-- Numeric evaluation with the three stage bits supplying 0/1 variable values. -/
def evalNat (s : Stage) : IR → ℕ
  | .zero => 0
  | .one => 1
  | .x => if s.1 then 1 else 0
  | .y => if s.2.1 then 1 else 0
  | .z => if s.2.2 then 1 else 0
  | .add l r => evalNat s l + evalNat s r

/-- Boolean evaluation of the same syntax, with addition interpreted as disjunction. -/
def evalBool (s : Stage) : IR → Bool
  | .zero => false
  | .one => true
  | .x => s.1
  | .y => s.2.1
  | .z => s.2.2
  | .add l r => evalBool s l || evalBool s r

def original : IR := .add .x (.add .y .z)
def middle : IR := .add .y .z
def optimized : IR := .z
def guardX : Stage := (false, true, true)
def guardY : Stage := (true, false, true)

/-- Expand the universal stage check into three finite Boolean quantifiers. -/
theorem guarded_cube_iff {Term Val : Type*} (eval : Stage → Term → Val)
    (p : Stage) (t₁ t₂ : Term) :
    GuardedEquiv eval p t₁ t₂ ↔
      ∀ x y z : Bool, (x, y, z) ≤ p → eval (x, y, z) t₁ = eval (x, y, z) t₂ := by
  constructor
  · exact fun h x y z hs => h (x, y, z) hs
  · rintro h ⟨x, y, z⟩ hs
    exact h x y z hs

/-- Numeric equality holds pointwise exactly under the intended stage restrictions. -/
theorem numeric_pointwise_table (x y z : Bool) :
    (evalNat (x, y, z) original = evalNat (x, y, z) middle ↔ x = false) ∧
    (evalNat (x, y, z) middle = evalNat (x, y, z) optimized ↔ y = false) ∧
    (evalNat (x, y, z) original = evalNat (x, y, z) optimized ↔ x = false ∧ y = false) := by
  cases x <;> cases y <;> cases z <;> decide

/-- Exact guarded-equivalence table over every numeric guard, including bottom and top. -/
theorem nat_guard_classification (p : Stage) :
    (GuardedEquiv evalNat p original middle ↔ p.1 = false) ∧
    (GuardedEquiv evalNat p middle optimized ↔ p.2.1 = false) ∧
    (GuardedEquiv evalNat p original optimized ↔ p.1 = false ∧ p.2.1 = false) := by
  simp only [guarded_cube_iff]
  rcases p with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> decide

/-- Universal substage checking yields the same exact guards for the Boolean evaluator. -/
theorem bool_guard_classification (p : Stage) :
    (GuardedEquiv evalBool p original middle ↔ p.1 = false) ∧
    (GuardedEquiv evalBool p middle optimized ↔ p.2.1 = false) ∧
    (GuardedEquiv evalBool p original optimized ↔ p.1 = false ∧ p.2.1 = false) := by
  simp only [guarded_cube_iff]
  rcases p with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> decide

/-- Concrete reflexivity for every term in the chain, under both interpretations. -/
theorem concrete_refl :
    GuardedEquiv evalNat ⊤ original original ∧ GuardedEquiv evalNat ⊤ middle middle ∧
    GuardedEquiv evalNat ⊤ optimized optimized ∧ GuardedEquiv evalBool ⊤ original original ∧
    GuardedEquiv evalBool ⊤ middle middle ∧ GuardedEquiv evalBool ⊤ optimized optimized := by
  simp only [guarded_cube_iff]
  decide

/-- Concrete symmetry at every guard under both interpretations. -/
theorem finite_symm (p : Stage) :
    (GuardedEquiv evalNat p original middle → GuardedEquiv evalNat p middle original) ∧
    (GuardedEquiv evalBool p original middle → GuardedEquiv evalBool p middle original) := by
  simp only [guarded_cube_iff]
  rcases p with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> decide

/-- All 64 guard pairs for each interpretation, keeping both rewrite hypotheses. -/
theorem finite_trans (p q : Stage) :
    (GuardedEquiv evalNat p original middle → GuardedEquiv evalNat q middle optimized →
      GuardedEquiv evalNat (p ⊓ q) original optimized) ∧
    (GuardedEquiv evalBool p original middle → GuardedEquiv evalBool q middle optimized →
      GuardedEquiv evalBool (p ⊓ q) original optimized) := by
  rw [(nat_guard_classification p).1, (nat_guard_classification q).2.1,
    (nat_guard_classification (p ⊓ q)).2.2,
    (bool_guard_classification p).1, (bool_guard_classification q).2.1,
    (bool_guard_classification (p ⊓ q)).2.2]
  rcases p with ⟨p₁, p₂, p₃⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases p₁ <;> cases p₂ <;> cases p₃ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- All 512 source/guard/guard combinations for each evaluator. -/
theorem finite_synthesis (a p q : Stage) :
    (GuardedEquiv evalNat p original middle → GuardedEquiv evalNat q middle optimized →
      evalNat (a ⊓ (synthesizeGuard a p ⊓ synthesizeGuard a q)) original =
        evalNat (a ⊓ (synthesizeGuard a p ⊓ synthesizeGuard a q)) optimized) ∧
    (GuardedEquiv evalBool p original middle → GuardedEquiv evalBool q middle optimized →
      evalBool (a ⊓ (synthesizeGuard a p ⊓ synthesizeGuard a q)) original =
        evalBool (a ⊓ (synthesizeGuard a p ⊓ synthesizeGuard a q)) optimized) := by
  simp only [guarded_cube_iff]
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases p with ⟨p₁, p₂, p₃⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases p₁ <;> cases p₂ <;>
    cases p₃ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- Both chains have satisfiable, proper guards whose meet remains nonbottom. -/
theorem concrete_rewrites :
    GuardedEquiv evalNat guardX original middle ∧ GuardedEquiv evalNat guardY middle optimized ∧
    GuardedEquiv evalNat (guardX ⊓ guardY) original optimized ∧
    GuardedEquiv evalBool guardX original middle ∧ GuardedEquiv evalBool guardY middle optimized ∧
    GuardedEquiv evalBool (guardX ⊓ guardY) original optimized := by
  simp only [guarded_cube_iff]
  decide

/-- Synthesizing the two conditional rewrites keeps z and removes exactly x and y. -/
theorem residual_stage_table (x y z : Bool) :
    let a : Stage := (x, y, z)
    let residual := synthesizeGuard a guardX ⊓ synthesizeGuard a guardY
    residual = (!x, !y, true) ∧ a ⊓ residual = (false, false, z) ∧
    evalNat (a ⊓ residual) original = (if z then 1 else 0) ∧
    evalNat (a ⊓ residual) optimized = (if z then 1 else 0) ∧
    evalBool (a ⊓ residual) original = z ∧ evalBool (a ⊓ residual) optimized = z := by
  dsimp only
  cases x <;> cases y <;> cases z <;> decide

/-- Nonbottom guarded equality has value 1, differs from the bottom value 0,
and does not imply equality at the original maximal stage. -/
theorem active_stage_witness :
    guardX ⊓ guardY = (false, false, true) ∧
    evalNat (false, false, true) original = 1 ∧ evalNat (false, false, true) optimized = 1 ∧
    evalNat (false, false, false) original = 0 ∧
    evalNat (true, true, true) original = 3 ∧ evalNat (true, true, true) optimized = 1 := by
  decide

/-- Joining the guards cannot replace their conjunction. -/
theorem guard_join_counterexample :
    ¬ GuardedEquiv evalNat (guardX ⊔ guardY) original optimized ∧
    ¬ GuardedEquiv evalBool (guardX ⊔ guardY) original optimized := by
  simp only [guarded_cube_iff]
  decide

/-- Either missing rewrite premise permits a failing endpoint equivalence. -/
theorem both_rewrites_required :
    (¬ GuardedEquiv evalNat ⊤ original middle ∧
      GuardedEquiv evalNat guardY middle optimized ∧
      ¬ GuardedEquiv evalNat (⊤ ⊓ guardY) original optimized) ∧
    (GuardedEquiv evalNat guardX original middle ∧
      ¬ GuardedEquiv evalNat ⊤ middle optimized ∧
      ¬ GuardedEquiv evalNat (guardX ⊓ ⊤) original optimized) := by
  simp only [guarded_cube_iff]
  decide

/-- Boolean equality at p itself is insufficient: a smaller forcing stage distinguishes terms. -/
theorem checking_only_guard_stage_fails :
    evalBool (true, false, true) original = evalBool (true, false, true) middle ∧
    Forces (true, false, false) (true, false, true) ∧
    evalBool (true, false, false) original ≠ evalBool (true, false, false) middle ∧
    ¬ GuardedEquiv evalBool (true, false, true) original middle := by
  simp only [guarded_cube_iff]
  unfold Forces
  decide

/-- Bottom forces every guard, so incompatible constant terms have no guard at all. -/
theorem constants_never_equiv (p : Stage) : ¬ GuardedEquiv evalNat p .zero .one := by
  intro h
  have hb := h (false, false, false) bot_le
  change (0 : ℕ) = 1 at hb
  cases hb

/-- Conservative supplied preconditions can synthesize a stricter guard than endpoint equality needs. -/
theorem residual_need_not_be_weakest :
    GuardedEquiv evalNat ⊥ original middle ∧ GuardedEquiv evalNat guardY middle optimized ∧
    synthesizeGuard (true, true, true) (⊥ : Stage) ⊓
      synthesizeGuard (true, true, true) guardY = (false, false, false) ∧
    GuardedEquiv evalNat (false, false, true) original optimized := by
  simp only [guarded_cube_iff]
  decide

end Round8

/-!
## Round 9: inter-block and loop-hoisted conditional rewrites

The definition and all four statements match the blueprint. `pullbackEval`
precomposes a target evaluator with `T.post`, which maps source stages into
the evaluator's domain. The admissible source guard is instead `T.pullback q`,
by adjunction. Weakening restricts stages using `p ≤ q`. No monotonicity or
naturality of the evaluator is assumed. Transport preserves guarded
equivalence, but need not reflect it when some target stages are unreachable.

The numeric and Boolean IR evaluators from Round 8 are transported across
the heterogeneous entry edge `(x,y) ↦ (y,false,x)`. The target guard 011
becomes source guard 10. Source 11 is restricted to 10, enters at 001,
and evaluates both original and middle terms to 1 (true for the Boolean
interpretation). Without the guard the numeric values are 2 and 1.

A new loop swaps y and z, preserving 011 while alternating 001 and 010.
Thus the hoisted rewrite remains equal for all iteration counts even though
the loop state changes. Independent numeric computation checks cover 64
weakening guard pairs, 8 pullback guards, 32 source/target pairs, and 3072
loop-hoisted cases at depths 0 through 5: 3176 cases. Both interpreters also
have exact transported guard tables and an all-natural hoisting witness.
Negative witnesses distinguish the two transfer directions, composition
order, and each required semantic hypothesis. No target placeholder or
Classical.choice dependency is used.
-/

namespace Round9

/-- Weakening restricts the set of stages that must be checked. -/
theorem equiv_weaken {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (p q : α) (t₁ t₂ : Term)
    (hpq : Forces p q) (h : GuardedEquiv eval q t₁ t₂) :
    GuardedEquiv eval p t₁ t₂ := by
  intro s hs
  exact h s (hs.trans hpq)

/-- Independent transport proof using the adjunction in the required direction. -/
theorem equiv_pullback {α β Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (evalβ : β → Term → Val)
    (q : β) (t₁ t₂ : Term) (h : GuardedEquiv evalβ q t₁ t₂) :
    GuardedEquiv (pullbackEval T evalβ) (T.pullback q) t₁ t₂ := by
  intro s hs
  exact h (T.post s) ((T.gc s q).mpr hs)

/-- Independent edge-synthesis proof at the transferred guarded stage. -/
theorem edge_synthesize {α β Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (evalβ : β → Term → Val)
    (a : α) (q : β) (t₁ t₂ : Term) (h : GuardedEquiv evalβ q t₁ t₂) :
    evalβ (T.post (a ⊓ synthesizeEdgeGuard T a q)) t₁ =
      evalβ (T.post (a ⊓ synthesizeEdgeGuard T a q)) t₂ := by
  exact h _ ((T.gc _ _).mpr (le_himp_iff'.mp le_rfl))

/-- Independent loop-hoisted rewrite proof for every finite iteration count. -/
theorem hoisted_rewrite {α β Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (E : CFGTransfer α β) (L : CFGTransfer β β) (evalβ : β → Term → Val)
    (a₀ : α) (inv q : β) (t₁ t₂ : Term)
    (hind : IsInductiveFor L inv q) (heq : GuardedEquiv evalβ q t₁ t₂) :
    ∀ n : ℕ,
      evalβ ((E.comp (L.iterate n)).post (a₀ ⊓ hoistLoopGuard E a₀ inv)) t₁ =
        evalβ ((E.comp (L.iterate n)).post (a₀ ⊓ hoistLoopGuard E a₀ inv)) t₂ := by
  intro n
  exact heq _ (Round6.hoist_target E L a₀ inv q hind n)

/-- Pulling an evaluator along identity preserves it definitionally. -/
theorem pullback_eval_id {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) : pullbackEval (CFGTransfer.id α) eval = eval := by
  rfl

/-- Evaluator precomposition follows the same source-to-target path order. -/
theorem pullback_eval_comp {α β γ Term Val : Type*}
    [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ]
    (T₁ : CFGTransfer α β) (T₂ : CFGTransfer β γ) (eval : γ → Term → Val) :
    pullbackEval (T₁.comp T₂) eval = pullbackEval T₁ (pullbackEval T₂ eval) := by
  rfl

open Round5 Round8

/-- A nonidentity loop that keeps x fixed and exchanges the remaining coordinates. -/
def swapYZ : CFGTransfer Stage Stage where
  post s := (s.1, s.2.2, s.2.1)
  pullback s := (s.1, s.2.2, s.2.1)
  gc := by
    rintro ⟨x₁, x₂, x₃⟩ ⟨q₁, q₂, q₃⟩
    cases x₁ <;> cases x₂ <;> cases x₃ <;>
      cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- Include the three-cycle to exercise both valid and invalid candidate invariants. -/
def loop (cyclic : Bool) : CFGTransfer Stage Stage :=
  if cyclic then Round4.loop true else swapYZ

/-- Finite expansion of guarded equivalence in the two-coordinate source domain. -/
theorem guarded_source_iff {Term Val : Type*} (eval : PreState → Term → Val)
    (p : PreState) (t₁ t₂ : Term) :
    GuardedEquiv eval p t₁ t₂ ↔
      ∀ x y : Bool, (x, y) ≤ p → eval (x, y) t₁ = eval (x, y) t₂ := by
  constructor
  · exact fun h x y hs => h (x, y) hs
  · rintro h ⟨x, y⟩ hs
    exact h x y hs

/-- Exact transported guard tables for both interpretations of the IR. -/
theorem upstream_guard_classification (p : PreState) :
    (GuardedEquiv (pullbackEval entry evalNat) p original middle ↔ p.2 = false) ∧
    (GuardedEquiv (pullbackEval entry evalBool) p original middle ↔ p.2 = false) := by
  simp only [guarded_source_iff]
  rcases p with ⟨x, y⟩
  cases x <;> cases y <;> decide

/-- The transported evaluators compute on the entry post-state, retaining source x. -/
theorem upstream_value_table (x y : Bool) :
    pullbackEval entry evalNat (x, y) original =
      (if y then 1 else 0) + (if x then 1 else 0) ∧
    pullbackEval entry evalNat (x, y) middle = (if x then 1 else 0) ∧
    pullbackEval entry evalBool (x, y) original = (y || x) ∧
    pullbackEval entry evalBool (x, y) middle = x := by
  cases x <;> cases y <;> decide

/-- All 64 pairs of downstream guards, retaining the stage-inclusion premise. -/
theorem finite_weaken (p q : Stage) :
    Forces p q → GuardedEquiv evalNat q original middle → GuardedEquiv evalNat p original middle := by
  rw [(nat_guard_classification q).1, (nat_guard_classification p).1]
  unfold Forces
  rcases p with ⟨p₁, p₂, p₃⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases p₁ <;> cases p₂ <;> cases p₃ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- Every downstream guard is tested against its transported source guard. -/
theorem finite_pullback (q : Stage) :
    GuardedEquiv evalNat q original middle →
      GuardedEquiv (pullbackEval entry evalNat) (entry.pullback q) original middle := by
  rw [(nat_guard_classification q).1, (upstream_guard_classification (entry.pullback q)).1]
  rcases q with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> decide

/-- All 32 source/target pairs for actual transferred term equality. -/
theorem finite_edge_synthesis (a : PreState) (q : Stage) :
    GuardedEquiv evalNat q original middle →
      evalNat (entry.post (a ⊓ synthesizeEdgeGuard entry a q)) original =
        evalNat (entry.post (a ⊓ synthesizeEdgeGuard entry a q)) middle := by
  rw [(nat_guard_classification q).1]
  rcases a with ⟨a₁, a₂⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases a₁ <;> cases a₂ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- Both loops, every source/invariant/target, and all six depths 0 through 5. -/
theorem finite_hoist (cyclic : Bool) (a₀ : PreState) (inv q : Stage) :
    IsInductiveFor (loop cyclic) inv q → GuardedEquiv evalNat q original middle →
      Round6.ThroughFive (fun n =>
        evalNat ((entry.comp ((loop cyclic).iterate n)).post
          (a₀ ⊓ hoistLoopGuard entry a₀ inv)) original =
        evalNat ((entry.comp ((loop cyclic).iterate n)).post
          (a₀ ⊓ hoistLoopGuard entry a₀ inv)) middle) := by
  rw [(nat_guard_classification q).1]
  unfold IsInductiveFor IsLoopInvariant Round6.ThroughFive
  rcases a₀ with ⟨a₁, a₂⟩
  rcases inv with ⟨i₁, i₂, i₃⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases cyclic <;> cases a₁ <;> cases a₂ <;> cases i₁ <;> cases i₂ <;>
    cases i₃ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- The edge guard is proper and nonbottom; it repairs a genuine downstream difference. -/
theorem interblock_active_witness :
    let a : PreState := (true, true)
    let g := synthesizeEdgeGuard entry a guardX
    let reached := entry.post (a ⊓ g)
    GuardedEquiv evalNat guardX original middle ∧
    GuardedEquiv (pullbackEval entry evalNat) (entry.pullback guardX) original middle ∧
    entry.pullback guardX = (true, false) ∧ g = (true, false) ∧
    reached = (false, false, true) ∧ evalNat reached original = 1 ∧ evalNat reached middle = 1 ∧
    evalBool reached original = true ∧ evalBool reached middle = true ∧
    evalNat (entry.post a) original ≠ evalNat (entry.post a) middle := by
  dsimp only
  simp only [guarded_cube_iff, guarded_source_iff]
  decide

/-- Source transport need not reflect equivalence: entry never reaches a stage with y=true. -/
theorem pullback_converse_fails :
    ¬ GuardedEquiv evalNat guardX middle optimized ∧
    GuardedEquiv (pullbackEval entry evalNat) (entry.pullback guardX) middle optimized := by
  simp only [guarded_cube_iff, guarded_source_iff]
  decide

/-- Reversing the guard-inclusion direction would incorrectly admit unrestricted stages. -/
theorem weakening_direction_matters :
    Forces guardX (⊤ : Stage) ∧ GuardedEquiv evalNat guardX original middle ∧
    ¬ GuardedEquiv evalNat ⊤ original middle := by
  simp only [guarded_cube_iff]
  unfold Forces
  decide

/-- A source stage permitted by the pullback guard must be evaluated through post. -/
theorem evaluator_direction_matters :
    let T := Round4.loop true
    let s : Stage := (false, true, false)
    Forces s (T.pullback guardX) ∧
    pullbackEval T evalNat s original = pullbackEval T evalNat s middle ∧
    evalNat (T.pullback s) original ≠ evalNat (T.pullback s) middle := by
  dsimp only
  unfold Forces
  decide

/-- Actual nonempty loop states alternate after the single preheader check. -/
theorem hoisted_state_trace :
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) guardX)
    IsInductiveFor swapYZ guardX guardX ∧ entered = (false, false, true) ∧
    (swapYZ.iterate 0).post entered = (false, false, true) ∧
    (swapYZ.iterate 1).post entered = (false, true, false) ∧
    (swapYZ.iterate 2).post entered = (false, false, true) ∧
    (swapYZ.iterate 5).post entered = (false, true, false) := by
  dsimp only
  unfold IsInductiveFor IsLoopInvariant
  decide

/-- Both interpretations admit this concrete rewrite for every natural iteration count. -/
theorem hoisted_rewrites_all_steps :
    ∀ n : ℕ,
      (evalNat ((entry.comp (swapYZ.iterate n)).post
        ((true, true) ⊓ hoistLoopGuard entry (true, true) guardX)) original =
       evalNat ((entry.comp (swapYZ.iterate n)).post
        ((true, true) ⊓ hoistLoopGuard entry (true, true) guardX)) middle) ∧
      (evalBool ((entry.comp (swapYZ.iterate n)).post
        ((true, true) ⊓ hoistLoopGuard entry (true, true) guardX)) original =
       evalBool ((entry.comp (swapYZ.iterate n)).post
        ((true, true) ⊓ hoistLoopGuard entry (true, true) guardX)) middle) := by
  intro n
  have hind : IsInductiveFor swapYZ guardX guardX := by
    unfold IsInductiveFor IsLoopInvariant
    decide
  exact ⟨hoisted_rewrite entry swapYZ evalNat (true, true) guardX guardX original middle
      hind ((nat_guard_classification guardX).1.mpr rfl) n,
    hoisted_rewrite entry swapYZ evalBool (true, true) guardX guardX original middle
      hind ((bool_guard_classification guardX).1.mpr rfl) n⟩

/-- Reversing entry/loop order changes a successful conditional rewrite into a failure. -/
theorem composition_order_matters :
    let E := Round4.loop true
    let g := hoistLoopGuard E (true, true, true) guardX
    g = (true, true, false) ∧
    evalNat ((E.comp swapYZ).post g) original = evalNat ((E.comp swapYZ).post g) middle ∧
    evalNat ((swapYZ.comp E).post g) original ≠ evalNat ((swapYZ.comp E).post g) middle := by
  dsimp only
  decide

/-- Entry establishes the rewrite condition, but a non-preserving loop can destroy it. -/
theorem preservation_required :
    let L := Round4.loop true
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) guardX)
    GuardedEquiv evalNat guardX original middle ∧ ¬ IsLoopInvariant L guardX ∧
    evalNat entered original = evalNat entered middle ∧
    evalNat (L.post entered) original ≠ evalNat (L.post entered) middle := by
  dsimp only
  simp only [guarded_cube_iff]
  unfold IsLoopInvariant
  decide

/-- A preserved invariant must also imply the rewrite condition. -/
theorem entailment_required :
    let inv : Stage := ⊤
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) inv)
    IsLoopInvariant swapYZ inv ∧ ¬ Forces inv guardX ∧
    GuardedEquiv evalNat guardX original middle ∧
    evalNat entered original ≠ evalNat entered middle := by
  dsimp only
  simp only [guarded_cube_iff]
  unfold IsLoopInvariant Forces
  decide

/-- Inductivity by itself cannot supply an invalid term-equivalence premise. -/
theorem rewrite_equivalence_required :
    let inv : Stage := ⊤
    let entered := entry.post ((true, true) ⊓ hoistLoopGuard entry (true, true) inv)
    IsInductiveFor swapYZ inv inv ∧ ¬ GuardedEquiv evalNat inv original middle ∧
    evalNat entered original ≠ evalNat entered middle := by
  dsimp only
  simp only [guarded_cube_iff]
  unfold IsInductiveFor IsLoopInvariant
  decide

end Round9

/-!
## Round 10: binary compositionality and diamond congruence

The definition and all four statements match the blueprint exactly.
`CompatibleOp2` supplies compositionality at each stage, for every operand
pair; the semantic combiner may depend on that stage. No associativity,
commutativity, or cross-stage law is required. Pullback-meet commutation
replaces equal guards, without assuming the evaluator preserves meets.
Diamond soundness establishes original/rewritten equality separately along
each path; it does not equate the values reached by different paths.

The concrete constructor is AST addition from Round 8, with both natural
addition and Boolean disjunction interpretations. The numeric congruence
test rewrites original -> middle in the left operand and middle -> optimized
in the right. At stage 001 both compound terms evaluate to 2, while at 111
they evaluate to 5 and 3. A syntax-sensitive operator demonstrates that the
compatibility premise is essential, and has no compatible semantic combiner.

The diamond paths have posts (x,z,false) and (y,z,z), with their respective
right adjoints. For target guard 011 and source 111, the individual guards
are 011 and 101 and their meet is the nonbottom stage 001. The paths reach
010 and 011. Addition congruence holds on both, with values 1 and 3, so the
within-path/cross-path distinction is observable. Independent numeric checks
cover 64 congruence guard pairs, 512 synthesis combinations, 128 pullback-meet
cases, and 64 diamond cases: 768 cases in total, plus explicit witnesses.
All proofs remain independent of the target placeholders and of choice.
-/

namespace Round10

/-- Independent congruence proof, applying both operand equalities at one stage. -/
theorem binary_congr {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (op : Term → Term → Term) (semOp : α → Val → Val → Val)
    (p₁ p₂ : α) (t₁ u₁ t₂ u₂ : Term)
    (hc : CompatibleOp2 eval op semOp)
    (h₁ : GuardedEquiv eval p₁ t₁ u₁) (h₂ : GuardedEquiv eval p₂ t₂ u₂) :
    GuardedEquiv eval (p₁ ⊓ p₂) (op t₁ t₂) (op u₁ u₂) := by
  intro s hs
  rw [hc s t₁ t₂, hc s u₁ u₂, h₁ s (hs.trans inf_le_left), h₂ s (hs.trans inf_le_right)]

/-- Independent synthesized congruence proof using the audited forcing equivalence. -/
theorem binary_synthesize {α Term Val : Type*} [HeytingAlgebra α]
    (eval : α → Term → Val) (op : Term → Term → Term) (semOp : α → Val → Val → Val)
    (a p₁ p₂ : α) (t₁ u₁ t₂ u₂ : Term)
    (hc : CompatibleOp2 eval op semOp)
    (h₁ : GuardedEquiv eval p₁ t₁ u₁) (h₂ : GuardedEquiv eval p₂ t₂ u₂) :
    eval (a ⊓ (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂)) (op t₁ t₂) =
      eval (a ⊓ (synthesizeGuard a p₁ ⊓ synthesizeGuard a p₂)) (op u₁ u₂) := by
  exact binary_congr eval op semOp p₁ p₂ t₁ u₁ t₂ u₂ hc h₁ h₂ _
    ((Round7.rewrite_chain a p₁ p₂ _).mpr le_rfl)

/-- Equal pulled-back guards give the same guarded-equivalence proposition. -/
theorem pullback_meet_commute {α β Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra β]
    (T : CFGTransfer α β) (evalβ : β → Term → Val) (q₁ q₂ : β) (t₁ t₂ : Term) :
    GuardedEquiv (pullbackEval T evalβ) (T.pullback (q₁ ⊓ q₂)) t₁ t₂ ↔
      GuardedEquiv (pullbackEval T evalβ) (T.pullback q₁ ⊓ T.pullback q₂) t₁ t₂ := by
  rw [Round3.pullback_meet]

/-- Each path establishes c, so the downstream equivalence applies separately to both. -/
theorem diamond_rewrite {α γ Term Val : Type*} [HeytingAlgebra α] [HeytingAlgebra γ]
    (P₁ P₂ : CFGTransfer α γ) (evalγ : γ → Term → Val)
    (a : α) (c : γ) (t₁ t₂ : Term) (h : GuardedEquiv evalγ c t₁ t₂) :
    let g := synthesizeEdgeGuard P₁ a c ⊓ synthesizeEdgeGuard P₂ a c
    evalγ (P₁.post (a ⊓ g)) t₁ = evalγ (P₁.post (a ⊓ g)) t₂ ∧
      evalγ (P₂.post (a ⊓ g)) t₁ = evalγ (P₂.post (a ⊓ g)) t₂ := by
  exact ⟨h _ ((P₁.gc _ _).mpr (le_himp_iff'.mp inf_le_left)),
    h _ ((P₂.gc _ _).mpr (le_himp_iff'.mp inf_le_right))⟩

open Round8

/-- Compatibility of actual AST addition holds for every stage and operand syntax. -/
theorem addition_compatible : CompatibleOp2 evalNat IR.add (fun _ x y => x + y) := by
  intro s l r
  rfl

/-- The same constructor is compatible with its Boolean interpretation. -/
theorem or_compatible : CompatibleOp2 evalBool IR.add (fun _ x y => x || y) := by
  intro s l r
  rfl

def compoundBefore : IR := .add original middle
def compoundAfter : IR := .add middle optimized
def diamondBefore : IR := .add original (.add .zero .z)
def diamondAfter : IR := .add middle .z

/-- Nonidentity, nonconstant converging transfers with independent source restrictions. -/
def path (first : Bool) : CFGTransfer Stage Stage where
  post s := if first then (s.1, s.2.2, false) else (s.2.1, s.2.2, s.2.2)
  pullback q := if first then (q.1, true, q.2.1) else (true, q.1, q.2.1 && q.2.2)
  gc := by
    rintro ⟨s₁, s₂, s₃⟩ ⟨q₁, q₂, q₃⟩
    cases first <;> cases s₁ <;> cases s₂ <;> cases s₃ <;>
      cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- Both directions of each path are nonidentity and nonconstant. -/
theorem paths_nontrivial (first : Bool) :
    (path first).post (false, true, false) ≠ (false, true, false) ∧
    (path first).pullback (false, false, false) ≠ (false, false, false) ∧
    (path first).post (false, false, false) ≠ (path first).post (true, true, true) ∧
    (path first).pullback (false, false, false) ≠ (path first).pullback (true, true, true) := by
  cases first <;> decide

/-- The right operand in the diamond example undergoes an actual zero-addition rewrite. -/
theorem zero_add_z_guard : GuardedEquiv evalNat guardX (.add .zero .z) .z := by
  rw [guarded_cube_iff]
  decide

/-- Construct the downstream diamond rewrite using binary compositionality. -/
theorem diamond_equivalence : GuardedEquiv evalNat guardX diamondBefore diamondAfter := by
  have h := binary_congr evalNat IR.add (fun _ x y => x + y) guardX guardX
    original middle (.add .zero .z) .z addition_compatible
    concrete_rewrites.1 zero_add_z_guard
  simpa only [inf_idem, diamondBefore, diamondAfter] using h

/-- Exact guard classification for the numeric two-operand congruence example. -/
theorem compound_guards (p : Stage) :
    GuardedEquiv evalNat p compoundBefore compoundAfter ↔ p.1 = false ∧ p.2.1 = false := by
  rw [guarded_cube_iff]
  rcases p with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> decide

/-- Exact downstream guard classification for the diamond's compound terms. -/
theorem diamond_guards (p : Stage) :
    GuardedEquiv evalNat p diamondBefore diamondAfter ↔ p.1 = false := by
  rw [guarded_cube_iff]
  rcases p with ⟨x, y, z⟩
  cases x <;> cases y <;> cases z <;> decide

/-- The two paths pull the downstream restriction back to different source coordinates. -/
theorem transported_guards (first : Bool) (p : Stage) :
    GuardedEquiv (pullbackEval (path first) evalNat) p diamondBefore diamondAfter ↔
      if first then p.1 = false else p.2.1 = false := by
  rw [guarded_cube_iff]
  rcases p with ⟨x, y, z⟩
  cases first <;> cases x <;> cases y <;> cases z <;> decide

/-- All 64 operand-guard pairs, keeping the two rewrite premises separate. -/
theorem finite_congr (p q : Stage) :
    GuardedEquiv evalNat p original middle → GuardedEquiv evalNat q middle optimized →
      GuardedEquiv evalNat (p ⊓ q) compoundBefore compoundAfter := by
  rw [(nat_guard_classification p).1, (nat_guard_classification q).2.1, compound_guards]
  rcases p with ⟨p₁, p₂, p₃⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases p₁ <;> cases p₂ <;> cases p₃ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- All 512 source/operand-guard/operand-guard synthesis cases. -/
theorem finite_synthesis (a p q : Stage) :
    GuardedEquiv evalNat p original middle → GuardedEquiv evalNat q middle optimized →
      evalNat (a ⊓ (synthesizeGuard a p ⊓ synthesizeGuard a q)) compoundBefore =
        evalNat (a ⊓ (synthesizeGuard a p ⊓ synthesizeGuard a q)) compoundAfter := by
  rw [(nat_guard_classification p).1, (nat_guard_classification q).2.1]
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases p with ⟨p₁, p₂, p₃⟩
  rcases q with ⟨q₁, q₂, q₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases p₁ <;> cases p₂ <;>
    cases p₃ <;> cases q₁ <;> cases q₂ <;> cases q₃ <;> decide

/-- All 128 path/target/target cases, computed independently of the general meet proof. -/
theorem finite_pullback_meet (first : Bool) (q₁ q₂ : Stage) :
    GuardedEquiv (pullbackEval (path first) evalNat) ((path first).pullback (q₁ ⊓ q₂))
      diamondBefore diamondAfter ↔
    GuardedEquiv (pullbackEval (path first) evalNat)
      ((path first).pullback q₁ ⊓ (path first).pullback q₂) diamondBefore diamondAfter := by
  simp only [transported_guards]
  rcases q₁ with ⟨u₁, u₂, u₃⟩
  rcases q₂ with ⟨v₁, v₂, v₃⟩
  cases first <;> cases u₁ <;> cases u₂ <;> cases u₃ <;>
    cases v₁ <;> cases v₂ <;> cases v₃ <;> decide

/-- All 64 source/target diamond cases for the compatible compound rewrite. -/
theorem finite_diamond (a c : Stage) :
    GuardedEquiv evalNat c diamondBefore diamondAfter →
      let g := synthesizeEdgeGuard (path true) a c ⊓ synthesizeEdgeGuard (path false) a c
      evalNat ((path true).post (a ⊓ g)) diamondBefore =
        evalNat ((path true).post (a ⊓ g)) diamondAfter ∧
      evalNat ((path false).post (a ⊓ g)) diamondBefore =
        evalNat ((path false).post (a ⊓ g)) diamondAfter := by
  rw [diamond_guards]
  rcases a with ⟨a₁, a₂, a₃⟩
  rcases c with ⟨c₁, c₂, c₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases c₁ <;> cases c₂ <;> cases c₃ <;> decide

/-- Both operand rewrites hold on proper guards; the shared stage gives nonzero compound values. -/
theorem active_binary_witness :
    GuardedEquiv evalNat guardX original middle ∧ GuardedEquiv evalNat guardY middle optimized ∧
    GuardedEquiv evalNat (guardX ⊓ guardY) compoundBefore compoundAfter ∧
    evalNat (false, false, true) compoundBefore = 2 ∧
    evalNat (false, false, true) compoundAfter = 2 ∧
    evalNat (true, true, true) compoundBefore = 5 ∧
    evalNat (true, true, true) compoundAfter = 3 := by
  simp only [guarded_cube_iff]
  decide

/-- Neither single operand guard, nor their join, suffices for this numeric rewrite. -/
theorem both_operand_guards_required :
    ¬ GuardedEquiv evalNat guardX compoundBefore compoundAfter ∧
    ¬ GuardedEquiv evalNat guardY compoundBefore compoundAfter ∧
    ¬ GuardedEquiv evalNat (guardX ⊔ guardY) compoundBefore compoundAfter := by
  simp only [guarded_cube_iff]
  decide

/-- A syntax-sensitive constructor that cannot respect semantic equality of its operands. -/
def badOp (left _right : IR) : IR :=
  match left with
  | .add .x _ => .one
  | _ => .zero

/-- No semantic combiner can distinguish the identical operand values seen here. -/
theorem badOp_has_no_semantics (semOp : Stage → ℕ → ℕ → ℕ) :
    ¬ CompatibleOp2 evalNat badOp semOp := by
  intro h
  have h₁ := h (false, false, true) original .zero
  have h₂ := h (false, false, true) middle .zero
  change (1 : ℕ) = semOp (false, false, true) 1 0 at h₁
  change (0 : ℕ) = semOp (false, false, true) 1 0 at h₂
  have impossible : (1 : ℕ) = 0 := h₁.trans h₂.symm
  cases impossible

/-- Operand equivalences alone do not imply congruence for an incompatible constructor. -/
theorem compatibility_required :
    GuardedEquiv evalNat guardX original middle ∧
    GuardedEquiv evalNat ⊤ IR.zero IR.zero ∧
    ¬ GuardedEquiv evalNat (guardX ⊓ ⊤) (badOp original .zero) (badOp middle .zero) := by
  simp only [guarded_cube_iff]
  decide

/-- Both diamond guards are restrictive; both reached stages are nonbottom.
Each path preserves the rewrite, but their common per-path values are different. -/
theorem active_diamond_witness :
    let a : Stage := (true, true, true)
    let g₁ := synthesizeEdgeGuard (path true) a guardX
    let g₂ := synthesizeEdgeGuard (path false) a guardX
    let s₁ := (path true).post (a ⊓ (g₁ ⊓ g₂))
    let s₂ := (path false).post (a ⊓ (g₁ ⊓ g₂))
    g₁ = guardX ∧ g₂ = guardY ∧ g₁ ⊓ g₂ = (false, false, true) ∧
    s₁ = (false, true, false) ∧ s₂ = (false, true, true) ∧
    evalNat s₁ diamondBefore = 1 ∧ evalNat s₁ diamondAfter = 1 ∧
    evalNat s₂ diamondBefore = 3 ∧ evalNat s₂ diamondAfter = 3 ∧
    evalNat s₁ diamondBefore ≠ evalNat s₂ diamondBefore := by
  dsimp only
  decide

/-- Keeping just one path's guard makes the other path's rewrite fail. -/
theorem each_path_guard_required :
    (evalNat ((path true).post guardX) diamondBefore =
      evalNat ((path true).post guardX) diamondAfter ∧
     evalNat ((path false).post guardX) diamondBefore ≠
      evalNat ((path false).post guardX) diamondAfter) ∧
    (evalNat ((path true).post guardY) diamondBefore ≠
      evalNat ((path true).post guardY) diamondAfter ∧
     evalNat ((path false).post guardY) diamondBefore =
      evalNat ((path false).post guardY) diamondAfter) := by
  decide

end Round10

/-!
## Round 11: concrete imperative state transitions

The definition and all four statements match the blueprint. `stateTransfer`
uses existential image for postconditions and substitution for pullbacks.
The adjunction is constructive and requires neither an inverse transition
nor a chosen preimage. The pointwise invariant condition is ordinary Hoare
preservation for a total transition function. The final target still uses
a predicate-indexed evaluator, rather than evaluating one arbitrarily
selected state; total transitions and finite-iteration safety do not assert
termination.

The concrete state is (counter, divisor) : Nat × Nat. Entry initializes the
counter to zero, and the loop increments it while retaining the divisor.
The proper invariant is divisor > 0. From an unrestricted preheader, the
hoisted guard accepts precisely positive divisors and rejects zero. Exact
reachability is proved for every n: reached n (c,d) iff c=n and d>0.
In particular (n,1) is reachable for every n, so the safety evidence is never
based only on an empty set of reachable states.

The conditional rewrite is c + d/d -> c + 1. A collecting evaluator maps a
state predicate to the predicate of possible numeric results, using only
existential witnesses. It makes no representative-state selection. Both
terms have exactly the possible result n+1 after n iterations. Natural
division is total, and d=0 makes the two terms differ; a loop that decrements
the divisor demonstrates why preservation is necessary. All results and
the stateTransfer definition are checked without sorryAx or Classical.choice.
-/

namespace Round11

/-- Independent verification of weakest-precondition substitution. -/
theorem pullback_apply {S₁ S₂ : Type*} (step : S₁ → S₂) (Q : S₂ → Prop) (s₁ : S₁) :
    (stateTransfer step).pullback Q s₁ ↔ Q (step s₁) := by
  rfl

/-- Independent verification of pointwise residual-guard implication. -/
theorem edge_guard_apply {S₁ S₂ : Type*} (step : S₁ → S₂)
    (P : S₁ → Prop) (Q : S₂ → Prop) (s₁ : S₁) :
    synthesizeEdgeGuard (stateTransfer step) P Q s₁ ↔ (P s₁ → Q (step s₁)) := by
  rfl

/-- The image-based invariant condition is exactly pointwise preservation. -/
theorem invariant_iff {S : Type*} (step : S → S) (inv : S → Prop) :
    IsLoopInvariant (stateTransfer step) inv ↔ ∀ s, inv s → inv (step s) := by
  exact (stateTransfer step).gc inv inv

/-- Independent specialization of the audited loop-hoisted rewrite theorem. -/
theorem hoisted_equiv {S₀ S Term Val : Type*} (init : S₀ → S) (step : S → S)
    (eval : (S → Prop) → Term → Val) (a₀ : S₀ → Prop) (inv q : S → Prop) (t₁ t₂ : Term)
    (hind : IsInductiveFor (stateTransfer step) inv q) (heq : GuardedEquiv eval q t₁ t₂) :
    ∀ n : ℕ,
      eval (((stateTransfer init).comp ((stateTransfer step).iterate n)).post
        (a₀ ⊓ hoistLoopGuard (stateTransfer init) a₀ inv)) t₁ =
      eval (((stateTransfer init).comp ((stateTransfer step).iterate n)).post
        (a₀ ⊓ hoistLoopGuard (stateTransfer init) a₀ inv)) t₂ := by
  exact Round9.hoisted_rewrite (stateTransfer init) (stateTransfer step) eval a₀ inv q t₁ t₂ hind heq

/-- A many-to-one reset confirms existential, rather than universal, image semantics. -/
theorem reset_image (P : ℕ → Prop) (m : ℕ) :
    (stateTransfer (fun _ : ℕ => 0)).post P m ↔ m = 0 ∧ ∃ n, P n := by
  constructor
  · rintro ⟨n, hm, hp⟩
    exact ⟨hm.symm, n, hp⟩
  · rintro ⟨rfl, n, hp⟩
    exact ⟨n, rfl, hp⟩

abbrev State := ℕ × ℕ

def init (d : ℕ) : State := (0, d)
def step (s : State) : State := (s.1 + 1, s.2)
def initial (_ : ℕ) : Prop := True
def positive (s : State) : Prop := 0 < s.2

/-- The actual predicate reached after guarded entry and n loop iterations. -/
def reached (n : ℕ) : State → Prop :=
  ((stateTransfer init).comp ((stateTransfer step).iterate n)).post
    (initial ⊓ hoistLoopGuard (stateTransfer init) initial positive)

/-- The divisor is unchanged by the loop, so positivity is inductive. -/
theorem positive_invariant : IsLoopInvariant (stateTransfer step) positive := by
  exact (invariant_iff step positive).mpr (fun _ h => h)

theorem positive_inductive : IsInductiveFor (stateTransfer step) positive positive := by
  exact ⟨positive_invariant, fun _ h => h⟩

/-- The preheader guard is precisely the nonzero-divisor test. -/
theorem entry_guard (d : ℕ) :
    hoistLoopGuard (stateTransfer init) initial positive d ↔ 0 < d := by
  change (True → 0 < d) ↔ 0 < d
  exact ⟨fun h => h True.intro, fun hd _ => hd⟩

/-- The guard is satisfiable and restrictive. -/
theorem entry_guard_examples :
    hoistLoopGuard (stateTransfer init) initial positive 1 ∧
    hoistLoopGuard (stateTransfer init) initial positive 2 ∧
    ¬ hoistLoopGuard (stateTransfer init) initial positive 0 := by
  simp only [entry_guard]
  decide

/-- Counter-dependent postconditions detect the increment in the pullback. -/
theorem counter_pullback_examples :
    (stateTransfer step).pullback (fun s => s.1 = 2) (1, 3) ∧
    ¬ (stateTransfer step).pullback (fun s => s.1 = 2) (2, 3) := by
  change (1 + 1 = 2) ∧ ¬ (2 + 1 = 2)
  decide

/-- The edge guard is conditional on its source predicate, including false antecedents. -/
theorem edge_guard_examples :
    let P : State → Prop := fun s => s.1 = 0
    let Q : State → Prop := fun s => s.1 = 1 ∧ 0 < s.2
    ¬ synthesizeEdgeGuard (stateTransfer step) P Q (0, 0) ∧
    synthesizeEdgeGuard (stateTransfer step) P Q (0, 2) ∧
    synthesizeEdgeGuard (stateTransfer step) P Q (1, 0) := by
  change ¬ (0 = 0 → 1 = 1 ∧ 0 < 0) ∧
    (0 = 0 → 1 = 1 ∧ 0 < 2) ∧ (1 = 0 → 2 = 1 ∧ 0 < 0)
  decide

/-- Exact reachability, including zero iterations and all positive input divisors. -/
theorem reached_iff (n c d : ℕ) : reached n (c, d) ↔ c = n ∧ 0 < d := by
  induction n generalizing c d with
  | zero =>
    constructor
    · rintro ⟨e, hstate, hguard⟩
      have he : 0 < e := hguard.2 True.intro
      cases hstate
      exact ⟨rfl, he⟩
    · rintro ⟨rfl, hd⟩
      exact ⟨d, rfl, True.intro, fun _ => hd⟩
  | succ n ih =>
    change (∃ s, step s = (c, d) ∧ reached n s) ↔ c = n + 1 ∧ 0 < d
    constructor
    · rintro ⟨⟨p, e⟩, hs, hp⟩
      rcases (ih p e).mp hp with ⟨rfl, he⟩
      cases hs
      exact ⟨rfl, he⟩
    · rintro ⟨rfl, hd⟩
      exact ⟨(n, d), rfl, (ih n d).mpr ⟨rfl, hd⟩⟩

/-- A concrete state exists at every iteration count; the invariant is not vacuous. -/
theorem reached_nonempty (n : ℕ) : ∃ s, reached n s := by
  exact ⟨(n, 1), (reached_iff n n 1).mpr ⟨rfl, by decide⟩⟩

/-- Exact traces include both valid states and rejected counter/divisor combinations. -/
theorem reachability_examples :
    reached 0 (0, 2) ∧ reached 1 (1, 2) ∧ reached 4 (4, 2) ∧
    ¬ reached 2 (1, 2) ∧ ¬ reached 3 (3, 0) := by
  simp only [reached_iff]
  decide

/-- Two arithmetic IR expressions differing only by the guarded division simplification. -/
inductive CounterExpr where
  | withDivision
  | increment

def scalarEval (s : State) : CounterExpr → ℕ
  | .withDivision => s.1 + s.2 / s.2
  | .increment => s.1 + 1

/-- Collect possible values constructively, without choosing any representative state. -/
def collectEval (P : State → Prop) (t : CounterExpr) : ℕ → Prop :=
  fun v => ∃ s, P s ∧ scalarEval s t = v

/-- The ordinary state-level arithmetic rewrite is valid on positive divisors. -/
theorem scalar_rewrite (s : State) (h : positive s) :
    scalarEval s .withDivision = scalarEval s .increment := by
  change s.1 + s.2 / s.2 = s.1 + 1
  rw [Nat.div_self h]

/-- Statewise equality lifts to equality of collected results at every forcing predicate. -/
theorem guarded_division : GuardedEquiv collectEval positive .withDivision .increment := by
  intro P hP
  funext v
  apply propext
  constructor
  · rintro ⟨s, hs, hv⟩
    exact ⟨s, hs, (scalar_rewrite s (hP s hs)).symm.trans hv⟩
  · rintro ⟨s, hs, hv⟩
    exact ⟨s, hs, (scalar_rewrite s (hP s hs)).trans hv⟩

/-- Concrete non-vacuous instantiation of the full all-iteration rewrite target. -/
theorem hoisted_rewrite_all :
    ∀ n : ℕ, collectEval (reached n) .withDivision = collectEval (reached n) .increment := by
  exact hoisted_equiv init step collectEval initial positive positive
    .withDivision .increment positive_inductive guarded_division

/-- The original expression has exactly the result n+1 after n iterations. -/
theorem collected_result (n v : ℕ) :
    collectEval (reached n) .withDivision v ↔ v = n + 1 := by
  constructor
  · rintro ⟨⟨c, d⟩, hs, hv⟩
    rcases (reached_iff n c d).mp hs with ⟨hc, hd⟩
    subst c
    change n + d / d = v at hv
    rw [Nat.div_self hd] at hv
    exact hv.symm
  · rintro rfl
    exact ⟨(n, 1), (reached_iff n n 1).mpr ⟨rfl, by decide⟩,
      scalar_rewrite (n, 1) (by change 0 < 1; decide)⟩

/-- The optimized expression has the same exact result, not merely an empty result set. -/
theorem optimized_result (n v : ℕ) :
    collectEval (reached n) .increment v ↔ v = n + 1 := by
  rw [← hoisted_rewrite_all n]
  exact collected_result n v

/-- Both states and observable values genuinely change during the loop. -/
theorem result_examples :
    collectEval (reached 0) .withDivision 1 ∧
    collectEval (reached 4) .withDivision 5 ∧
    collectEval (reached 4) .increment 5 ∧
    ¬ collectEval (reached 4) .withDivision 1 := by
  simp only [collected_result, optimized_result]
  decide

/-- The unrestricted rewrite fails on a concrete singleton containing a zero divisor. -/
theorem zero_divisor_rejected :
    ¬ GuardedEquiv collectEval (fun _ => True) .withDivision .increment := by
  intro h
  have heq := h (fun s => s = (0, 0)) (fun _ _ => True.intro)
  have hv : collectEval (fun s => s = (0, 0)) .withDivision 0 :=
    ⟨(0, 0), rfl, by decide⟩
  have hw : collectEval (fun s => s = (0, 0)) .increment 0 := heq ▸ hv
  rcases hw with ⟨s, hs, hv⟩
  subst s
  change (1 : ℕ) = 0 at hv
  cases hv

/-- An intentionally invalid loop changes the divisor as well as the counter. -/
def badStep (s : State) : State := (s.1 + 1, s.2 - 1)

/-- Positivity would not be preserved by this different transition. -/
theorem bad_step_not_invariant : ¬ IsLoopInvariant (stateTransfer badStep) positive := by
  intro h
  have hb := (invariant_iff badStep positive).mp h (0, 1) (by change 0 < 1; decide)
  change 0 < 0 at hb
  cases hb

/-- A positive entry can pass the first iteration yet lose the rewrite after the second. -/
theorem bad_step_trace :
    let entered := init 2
    let first := badStep entered
    let second := badStep first
    hoistLoopGuard (stateTransfer init) initial positive 2 ∧
    first = (1, 1) ∧ second = (2, 0) ∧
    scalarEval first .withDivision = 2 ∧ scalarEval first .increment = 2 ∧
    scalarEval second .withDivision = 2 ∧ scalarEval second .increment = 3 := by
  dsimp only
  rw [entry_guard]
  decide

end Round11


/-!
## Milestone 1: Round 1 Gate 1 audit (historical contract)

Review artifact: reviews/M1-prelock.md. The original Round 1 obligations are constructively
satisfiable, but they permit the fixture-specific optimizer below. This is an
adversarial existence witness, not a proposed implementation of the compiler.
The exact benchmark/context combinations improve, while a renamed benchmark
remains unchanged. All compiler-dependent obligations are packaged together
in CompilerObligations; the three independent TCB bridge/compatibility
obligations are also proved here.

The tests reject a global identity pass, always-false synthesis, always-imp
synthesis, a false-guard fallback, in-context trap-to-UB changes, and dropping
a strict failing operand. They retain the original zero-divisor trap under
the unknown context, and exhibit real positive reductions at a satisfying
environment. Dynamic cost witnesses refer to the abstract IR observer;
the separate runtime traversal caveat is documented in the review.
No declaration here invokes a target compiler stub or target theorem.
-/

namespace M1

def nz : GuardIR := .nonZero (.var 0)
def fastBench : Expr :=
  .add (.uncheckedDiv (.pure (.var 1)) (.pure (.var 0))) (.pure (.var 2))
def guardedBench : Expr := .iteGuard nz fastBench m1BenchExpr

theorem fast_sound (env : Env) (h : env 0 ≠ 0) :
    evalExpr env fastBench = evalExpr env m1BenchExpr := by
  simp [fastBench, m1BenchExpr, evalExpr, evalPure, h, Int.mul_ediv_cancel]
theorem cancel_sound (env : Env) (h : env 0 ≠ 0) :
    evalExpr env (.pure (.var 1)) = evalExpr env m1CancelExpr := by
  simp [m1CancelExpr, evalExpr, evalPure, h, Int.mul_ediv_cancel]
theorem guarded_sound (env : Env) :
    evalExpr env guardedBench = evalExpr env m1BenchExpr := by
  by_cases h : env 0 = 0
  · simp [guardedBench, nz, m1BenchExpr, evalExpr, evalGuard, evalPure, h]
  · simp [guardedBench, nz, fastBench, m1BenchExpr, evalExpr, evalGuard, evalPure,
      h, Int.mul_ediv_cancel]
/-- A deliberately fixture-specific optimizer: every other expression is returned unchanged. -/
def opt (ctx : GuardIR) (e : Expr) : Expr :=
  if ctx = nz then
    if e = m1BenchExpr then fastBench
    else if e = m1CancelExpr then .pure (.var 1)
    else e
  else if ctx = .top ∧ e = m1BenchExpr then guardedBench else e
theorem opt_sound (ctx : GuardIR) (e : Expr) (env : Env)
    (hctx : evalGuard env ctx = true) :
    evalExpr env (opt ctx e) = evalExpr env e := by
  by_cases hc : ctx = nz
  · subst ctx
    have hn : env 0 ≠ 0 := by
      change decide (env 0 ≠ 0) = true at hctx
      exact of_decide_eq_true hctx
    by_cases hb : e = m1BenchExpr
    · subst e
      simpa [opt] using fast_sound env hn
    · by_cases hx : e = m1CancelExpr
      · subst e
        simpa [opt, hb] using cancel_sound env hn
      · simp [opt, hb, hx]
  · by_cases ht : ctx = .top ∧ e = m1BenchExpr
    · rcases ht with ⟨rfl, rfl⟩
      simpa [opt, nz] using guarded_sound env
    · simp [opt, hc, ht]

/-- Correct synthesis with only syntactic-equality discharge; other residuals remain implications. -/
def synth (a b : GuardIR) : GuardIR := if a = b then .top else .imp a b
theorem synth_eval (a b : GuardIR) (env : Env) :
    evalGuard env (synth a b) = ((!evalGuard env a) || evalGuard env b) := by
  unfold synth
  split
  · rename_i h
    subst b
    cases evalGuard env a <;> rfl
  · rfl
theorem synth_denote (a b : GuardIR) :
    denoteGuard (synth a b) = synthesizeGuard (denoteGuard a) (denoteGuard b) := by
  funext env
  apply propext
  change evalGuard env (synth a b) = true ↔ (evalGuard env a = true → evalGuard env b = true)
  rw [synth_eval]
  cases evalGuard env a <;> cases evalGuard env b <;> decide
theorem synth_universal (a b : GuardIR) (g : Env → Prop) :
    denoteGuard a ⊓ g ≤ denoteGuard b ↔ g ≤ denoteGuard (synth a b) := by
  rw [synth_denote]
  exact le_himp_iff'.symm
theorem synth_discharge (p : PureExpr) : synth (.nonZero p) (.nonZero p) = .top := by
  simp [synth]

theorem known_elim (env : Env) :
    checkedDivCount (opt nz m1BenchExpr) = 0 ∧
    guardBranchCount (opt nz m1BenchExpr) = 0 ∧ execCheckCost env (opt nz m1BenchExpr) = 0 := by
  by_cases h : env 0 = 0 <;>
    simp [opt, fastBench, checkedDivCount, guardBranchCount, execCheckCost, evalExpr, evalPure, h]
theorem cancel_elim : divOpCount (opt nz m1CancelExpr) = 0 := by
  decide
theorem unknown_dedup (env : Env) (h : env 0 ≠ 0) :
    execCheckCost env (opt .top m1BenchExpr) ≤ 1 ∧ execCheckCost env m1BenchExpr = 2 := by
  simp [opt, nz, guardedBench, fastBench, m1BenchExpr, execCheckCost, guardEvalCost,
    evalGuard, evalExpr, evalPure, h]
theorem zero_trap (env : Env) (h : env 0 = 0) :
    evalExpr env (opt .top m1BenchExpr) = .trap := by
  simp [opt, nz, guardedBench, m1BenchExpr, evalGuard, evalExpr, evalPure, h]

theorem lift_bridge {S Term Out : Type*} (run : S → Term → Out)
    (P : S → Prop) (t₁ t₂ : Term) :
    GuardedEquiv (liftEval run) P t₁ t₂ ↔ ∀ s, P s → run s t₁ = run s t₂ := by
  constructor
  · intro h s hs
    have he := h P le_rfl
    have hout : liftEval run P t₂ s (run s t₁) :=
      Eq.mp (congrFun (congrFun he s) (run s t₁)) ⟨hs, rfl⟩
    exact hout.2.symm
  · intro h Q hQP
    funext s out
    apply propext
    constructor
    · rintro ⟨hs, he⟩
      exact ⟨hs, (h s (hQP s hs)).symm.trans he⟩
    · rintro ⟨hs, he⟩
      exact ⟨hs, (h s (hQP s hs)).trans he⟩

theorem lift_binary_compatible {Term : Type*} (run : Env → Term → Outcome)
    (op : Term → Term → Term) (f : Int → Int → Outcome)
    (hop : ∀ env l r, run env (op l r) = bindOutcome2 f (run env l) (run env r)) :
    CompatibleOp2 (liftEval run) op (liftBinarySem f) := by
  intro P l r
  funext env out
  apply propext
  constructor
  · rintro ⟨hp, he⟩
    exact ⟨run env l, run env r, ⟨hp, rfl⟩, ⟨hp, rfl⟩, (hop env l r).symm.trans he⟩
  · rintro ⟨o₁, o₂, ⟨hp, h₁⟩, ⟨_, h₂⟩, he⟩
    refine ⟨hp, ?_⟩
    rw [hop, h₁, h₂]
    exact he

theorem addition_compatible :
    CompatibleOp2 (liftEval evalExpr) Expr.add (liftBinarySem (fun x y => .val (x + y))) := by
  exact lift_binary_compatible evalExpr Expr.add _ (fun _ _ _ => rfl)
theorem checked_division_compatible :
    CompatibleOp2 (liftEval evalExpr) Expr.checkedDiv
      (liftBinarySem (fun x y => if y = 0 then .trap else .val (x / y))) := by
  exact lift_binary_compatible evalExpr Expr.checkedDiv _ (fun _ _ _ => rfl)

theorem opt_guarded (ctx : GuardIR) (e : Expr) :
    GuardedEquiv (liftEval evalExpr) (denoteGuard ctx) (opt ctx e) e := by
  exact (lift_bridge evalExpr (denoteGuard ctx) (opt ctx e) e).mpr (opt_sound ctx e)

/-- The same benchmark shape with renamed variables, outside the candidate's exact fixtures. -/
def renamedBench : Expr :=
  .add
    (.checkedDiv (.pure (.var 2)) (.pure (.var 3)))
    (.checkedDiv (.mul (.pure (.var 4)) (.pure (.var 3))) (.pure (.var 3)))
theorem renamed_untouched :
    opt (.nonZero (.var 3)) renamedBench = renamedBench := by
  decide
theorem renamed_still_checks :
    checkedDivCount (opt (.nonZero (.var 3)) renamedBench) = 2 := by
  decide


theorem unsimplified_top_residual (p : PureExpr) :
    synth .top (.nonZero p) = .imp .top (.nonZero p) := by
  rfl

/-- The nine original Round 1 compiler obligations, before the parametric revision.
The bridge and the two compatibility obligations are proved independently above. -/
structure CompilerObligations
    (synthFn : GuardIR → GuardIR → GuardIR) (optFn : GuardIR → Expr → Expr) : Prop where
  guardDenote : ∀ a b, denoteGuard (synthFn a b) = synthesizeGuard (denoteGuard a) (denoteGuard b)
  universal : ∀ a b (g : Env → Prop),
    denoteGuard a ⊓ g ≤ denoteGuard b ↔ g ≤ denoteGuard (synthFn a b)
  selfDischarge : ∀ p, synthFn (.nonZero p) (.nonZero p) = .top
  guarded : ∀ ctx e, GuardedEquiv (liftEval evalExpr) (denoteGuard ctx) (optFn ctx e) e
  sound : ∀ ctx e env, evalGuard env ctx = true → evalExpr env (optFn ctx e) = evalExpr env e
  known : ∀ env, checkedDivCount (optFn (.nonZero (.var 0)) m1BenchExpr) = 0 ∧
    guardBranchCount (optFn (.nonZero (.var 0)) m1BenchExpr) = 0 ∧
    execCheckCost env (optFn (.nonZero (.var 0)) m1BenchExpr) = 0
  cancel : divOpCount (optFn (.nonZero (.var 0)) m1CancelExpr) = 0
  dedup : ∀ env, env 0 ≠ 0 →
    execCheckCost env (optFn .top m1BenchExpr) ≤ 1 ∧ execCheckCost env m1BenchExpr = 2
  trap : ∀ env, env 0 = 0 → evalExpr env (optFn .top m1BenchExpr) = .trap

theorem candidate_obligations : CompilerObligations synth opt where
  guardDenote := synth_denote
  universal := synth_universal
  selfDischarge := synth_discharge
  guarded := opt_guarded
  sound := opt_sound
  known := known_elim
  cancel := cancel_elim
  dedup := unknown_dedup
  trap := zero_trap

theorem compiler_obligations_satisfiable :
    ∃ (synthFn : GuardIR → GuardIR → GuardIR) (optFn : GuardIR → Expr → Expr),
      CompilerObligations synthFn optFn := by
  exact ⟨synth, opt, candidate_obligations⟩

def positiveEnv : Env := fun v => if v = 0 then 2 else if v = 1 then 7 else 3
def zeroEnv : Env := fun _ => 0

theorem positive_reduction_witness :
    evalGuard positiveEnv nz = true ∧
    evalExpr positiveEnv m1BenchExpr = .val 6 ∧
    evalExpr positiveEnv (opt nz m1BenchExpr) = .val 6 ∧
    evalExpr positiveEnv (opt .top m1BenchExpr) = .val 6 ∧
    execCheckCost positiveEnv m1BenchExpr = 2 ∧
    execCheckCost positiveEnv (opt nz m1BenchExpr) = 0 ∧
    execCheckCost positiveEnv (opt .top m1BenchExpr) = 1 := by
  decide

theorem zero_trap_witness :
    evalGuard zeroEnv nz = false ∧
    evalExpr zeroEnv m1BenchExpr = .trap ∧
    evalExpr zeroEnv (opt .top m1BenchExpr) = .trap ∧
    execCheckCost zeroEnv m1BenchExpr = 1 ∧
    execCheckCost zeroEnv (opt .top m1BenchExpr) = 2 := by
  decide

/-- Undefined behavior outside a false optimization context is not ruled out by contextual soundness. -/
theorem outside_context_ub :
    evalGuard zeroEnv nz = false ∧ evalExpr zeroEnv (opt nz m1BenchExpr) = .ub := by
  decide

theorem identity_rejected (synthFn : GuardIR → GuardIR → GuardIR) :
    ¬ CompilerObligations synthFn (fun _ e => e) := by
  intro h
  have bad := (h.known zeroEnv).1
  change (2 : ℕ) = 0 at bad
  cases bad

theorem constant_bot_rejected (optFn : GuardIR → Expr → Expr) :
    ¬ CompilerObligations (fun _ _ => .bot) optFn := by
  intro h
  have he := congrFun (h.guardDenote .top .top) zeroEnv
  have hb : denoteGuard .bot zeroEnv := Eq.mpr he (fun _ => rfl)
  change false = true at hb
  cases hb

theorem raw_imp_rejected (optFn : GuardIR → Expr → Expr) :
    ¬ CompilerObligations GuardIR.imp optFn := by
  intro h
  have bad := h.selfDischarge (.var 0)
  cases bad

theorem false_fallback_still_checks :
    checkedDivCount (.iteGuard .bot fastBench m1BenchExpr) = 2 ∧
    guardBranchCount (.iteGuard .bot fastBench m1BenchExpr) = 1 ∧
    execCheckCost positiveEnv (.iteGuard .bot fastBench m1BenchExpr) = 2 := by
  decide

def trapExpr : Expr := .checkedDiv (.pure (.lit 1)) (.pure (.lit 0))
def ubExpr : Expr := .uncheckedDiv (.pure (.lit 1)) (.pure (.lit 0))
def zeroExpr : Expr := .pure (.lit 0)

theorem strict_outcomes :
    evalExpr zeroEnv (.mul zeroExpr trapExpr) = .trap ∧
    evalExpr zeroEnv (.mul zeroExpr ubExpr) = .ub ∧
    evalExpr zeroEnv (.add trapExpr ubExpr) = .trap ∧
    evalExpr zeroEnv (.add ubExpr trapExpr) = .ub ∧
    evalExpr zeroEnv (.iteGuard .bot ubExpr (.pure (.lit 7))) = .val 7 := by
  decide

theorem short_circuit_costs :
    execCheckCost zeroEnv (.add trapExpr trapExpr) = 1 ∧
    execCheckCost zeroEnv (.add ubExpr trapExpr) = 0 ∧
    execCheckCost zeroEnv (.checkedDiv (.pure (.lit 1)) trapExpr) = 1 ∧
    execCheckCost zeroEnv (.iteGuard .bot ubExpr (.pure (.lit 7))) = 0 := by
  decide

theorem guard_short_circuit :
    evalGuard zeroEnv (.imp nz .bot) = true ∧
    evalGuard positiveEnv (.imp nz .bot) = false ∧
    guardEvalCost positiveEnv (.conj .bot nz) = 0 ∧
    guardEvalCost positiveEnv (.imp .bot nz) = 0 ∧
    guardEvalCost positiveEnv (.imp .top nz) = 1 ∧
    guardEvalCost positiveEnv (.conj nz (.eq (.var 1) (.var 2))) = 2 ∧
    guardEvalCost zeroEnv (.conj nz (.eq (.var 1) (.var 2))) = 1 := by
  decide

theorem trap_to_ub_rejected :
    ¬ GuardedEquiv (liftEval evalExpr) (denoteGuard .top) trapExpr ubExpr := by
  intro h
  have bad := (lift_bridge evalExpr (denoteGuard .top) trapExpr ubExpr).mp h zeroEnv rfl
  cases bad

theorem dropping_strict_operand_rejected :
    ¬ GuardedEquiv (liftEval evalExpr) (denoteGuard .top) (.mul zeroExpr trapExpr) zeroExpr := by
  intro h
  have bad := (lift_bridge evalExpr (denoteGuard .top) (.mul zeroExpr trapExpr) zeroExpr).mp h zeroEnv rfl
  cases bad

theorem integer_division_scope :
    evalExpr zeroEnv (.checkedDiv (.pure (.lit (-3))) (.pure (.lit 2))) = .val (-2) := by
  decide

end M1


/-!
## Milestone 1: Round 2 pre-lock re-review

The original fixture-only M1.opt is preserved above as a historical witness.
The strengthened parametric contract below rejects it independently of the
guard synthesizer. The new synthesizer normalizes the required residual forms,
and the optimizer recursively rewrites arbitrary expression subtrees under
known nonzero contexts. Its top-context rule recognizes a shared-divisor
shape over arbitrary PureExpr operands, not fixed benchmark names/variables.
UpdatedObligations packages every original and new compiler-dependent law;
the independent lifting/compatibility obligations remain proved in M1.

The candidate is total and computable, with direct semantic and capability
proofs. The renamed/compound/nested examples have satisfying contexts and
real outcome/check reductions. No target compiler or theorem stub is invoked.
The source's final command audits all named RedTeam declarations and the
imported Defs module transitively, fails on forbidden dependencies, and emits
the records consumed by scripts/check_axioms.py.
-/

namespace M1R2

def hasNZ (ctx : GuardIR) (p : PureExpr) : Bool :=
  match ctx with
  | .nonZero q => decide (q = p)
  | .conj l r => hasNZ l p || hasNZ r p
  | _ => false

theorem hasNZ_sound (ctx : GuardIR) (p : PureExpr) (env : Env) :
    hasNZ ctx p = true → evalGuard env ctx = true → evalPure env p ≠ 0 := by
  induction ctx with
  | top => simp [hasNZ]
  | bot => simp [hasNZ]
  | eq l r => simp [hasNZ]
  | imp l r _ _ => simp [hasNZ]
  | nonZero q =>
    intro h hc
    have heq : q = p := of_decide_eq_true h
    subst q
    exact of_decide_eq_true hc
  | conj l r ihl ihr =>
    intro h hc
    simp only [hasNZ, Bool.or_eq_true] at h
    simp only [evalGuard, Bool.and_eq_true] at hc
    rcases h with hl | hr
    · exact ihl hl hc.1
    · exact ihr hr hc.2

@[simp] theorem hasNZ_self (p : PureExpr) : hasNZ (.nonZero p) p = true := by
  simp [hasNZ]
@[simp] theorem hasNZ_left (p : PureExpr) (rest : GuardIR) :
    hasNZ (.conj (.nonZero p) rest) p = true := by
  simp [hasNZ]
@[simp] theorem hasNZ_right (rest : GuardIR) (p : PureExpr) :
    hasNZ (.conj rest (.nonZero p)) p = true := by
  simp [hasNZ]
def shrink (b : GuardIR) : GuardIR :=
  match b with
  | .conj l r => if l = r then l else .conj l r
  | _ => b

theorem shrink_eval (b : GuardIR) (env : Env) : evalGuard env (shrink b) = evalGuard env b := by
  cases b <;> try rfl
  rename_i l r
  by_cases h : l = r
  · subst r
    simp [shrink, evalGuard]
  · simp [shrink, h]

def synthNZ (a : GuardIR) (p : PureExpr) : GuardIR :=
  if hasNZ a p then .top else .imp a (.nonZero p)

theorem synthNZ_eval (a : GuardIR) (p : PureExpr) (env : Env) :
    evalGuard env (synthNZ a p) = ((!evalGuard env a) || evalGuard env (.nonZero p)) := by
  unfold synthNZ
  split
  · rename_i h
    cases ha : evalGuard env a with
    | false => rfl
    | true =>
      have hp := hasNZ_sound a p env h ha
      simp [evalGuard, hp]
  · rfl

def synth (a b : GuardIR) : GuardIR :=
  match a, b with
  | .bot, _ => .top
  | _, .top => .top
  | .top, _ => shrink b
  | _, .nonZero p => synthNZ a p
  | _, _ => .imp a b

theorem synth_eval (a b : GuardIR) (env : Env) :
    evalGuard env (synth a b) = ((!evalGuard env a) || evalGuard env b) := by
  cases a <;> cases b <;> simp [synth, shrink_eval, synthNZ_eval, evalGuard]

theorem synth_denote (a b : GuardIR) :
    denoteGuard (synth a b) = synthesizeGuard (denoteGuard a) (denoteGuard b) := by
  funext env
  apply propext
  change evalGuard env (synth a b) = true ↔ (evalGuard env a = true → evalGuard env b = true)
  rw [synth_eval]
  cases evalGuard env a <;> cases evalGuard env b <;> decide

theorem synth_universal (a b : GuardIR) (g : Env → Prop) :
    denoteGuard a ⊓ g ≤ denoteGuard b ↔ g ≤ denoteGuard (synth a b) := by
  rw [synth_denote]
  exact le_himp_iff'.symm

theorem synth_self (p : PureExpr) : synth (.nonZero p) (.nonZero p) = .top := by
  simp [synth, synthNZ]
theorem synth_top_right (a : GuardIR) : synth a .top = .top := by
  cases a <;> rfl
theorem synth_bot_left (b : GuardIR) : synth .bot b = .top := by
  rfl
theorem synth_top_left_nonZero (p : PureExpr) : synth .top (.nonZero p) = .nonZero p := by
  rfl
theorem synth_conj_left (p : PureExpr) (rest : GuardIR) :
    synth (.conj (.nonZero p) rest) (.nonZero p) = .top := by
  simp [synth, synthNZ]
theorem synth_conj_right (rest : GuardIR) (p : PureExpr) :
    synth (.conj rest (.nonZero p)) (.nonZero p) = .top := by
  simp [synth, synthNZ]
theorem synth_dedup (p : PureExpr) :
    synth .top (.conj (.nonZero p) (.nonZero p)) = .nonZero p := by
  simp [synth, shrink]
/-- Simplify checked division with a pure denominator known nonzero in context. -/
def smartDiv (ctx : GuardIR) (num div : Expr) : Expr :=
  match num, div with
  | .mul (.pure x) (.pure y), .pure d =>
    if hasNZ ctx d then
      if y = d then .pure x
      else if x = d then .pure y
      else .uncheckedDiv num div
    else .checkedDiv num div
  | _, .pure d => if hasNZ ctx d then .uncheckedDiv num div else .checkedDiv num div
  | _, _ => .checkedDiv num div

theorem smartDiv_sound (ctx : GuardIR) (num div : Expr) (env : Env)
    (hc : evalGuard env ctx = true) :
    evalExpr env (smartDiv ctx num div) = evalExpr env (.checkedDiv num div) := by
  unfold smartDiv
  split
  · rename_i x y d
    split
    · rename_i hn
      have hd := hasNZ_sound ctx d env hn hc
      split
      · rename_i hy
        subst y
        simp [evalExpr, hd, Int.mul_ediv_cancel]
      · split
        · rename_i hx
          subst x
          simp [evalExpr, hd, Int.mul_comm, Int.mul_ediv_cancel]
        · simp [evalExpr, hd]
    · rfl
  · rename_i num' div' d hnum
    split
    · rename_i hn
      have hd := hasNZ_sound ctx d env hn hc
      simp [evalExpr, hd]
    · rfl
  · rfl


/-- Recursive optimizer for arbitrary expression subtrees under a known context. -/
def core (ctx : GuardIR) : Expr → Expr
  | .pure p => .pure p
  | .add l r => .add (core ctx l) (core ctx r)
  | .sub l r => .sub (core ctx l) (core ctx r)
  | .mul l r => .mul (core ctx l) (core ctx r)
  | .checkedDiv l r => smartDiv ctx (core ctx l) (core ctx r)
  | .uncheckedDiv l r => .uncheckedDiv (core ctx l) (core ctx r)
  | .iteGuard g t f => .iteGuard g (core ctx t) (core ctx f)

theorem core_sound (ctx : GuardIR) (e : Expr) (env : Env)
    (hc : evalGuard env ctx = true) : evalExpr env (core ctx e) = evalExpr env e := by
  induction e with
  | pure p => rfl
  | add l r ihl ihr => simp only [core, evalExpr, ihl, ihr]
  | sub l r ihl ihr => simp only [core, evalExpr, ihl, ihr]
  | mul l r ihl ihr => simp only [core, evalExpr, ihl, ihr]
  | uncheckedDiv l r ihl ihr => simp only [core, evalExpr, ihl, ihr]
  | checkedDiv l r ihl ihr =>
    simp only [core]
    rw [smartDiv_sound ctx _ _ env hc]
    simp only [evalExpr, ihl, ihr]
  | iteGuard g t f iht ihf => simp only [core, evalExpr, iht, ihf]

theorem smartDiv_top (num div : Expr) :
    smartDiv .top num div = .checkedDiv num div := by
  unfold smartDiv
  split <;> simp [hasNZ]

theorem core_top (e : Expr) : core .top e = e := by
  induction e with
  | pure p => rfl
  | add l r ihl ihr => simp [core, ihl, ihr]
  | sub l r ihl ihr => simp [core, ihl, ihr]
  | mul l r ihl ihr => simp [core, ihl, ihr]
  | checkedDiv l r ihl ihr => simp [core, ihl, ihr, smartDiv_top]
  | uncheckedDiv l r ihl ihr => simp [core, ihl, ihr]
  | iteGuard g t f iht ihf => simp [core, iht, ihf]


def fastDual (x y d : PureExpr) : Expr :=
  .add (.uncheckedDiv (.pure x) (.pure d)) (.pure y)
def guardedDual (x y d : PureExpr) : Expr :=
  .iteGuard (.nonZero d) (fastDual x y d) (mkDualDivExpr x y d)

theorem fastDual_sound (x y d : PureExpr) (env : Env) (hd : evalPure env d ≠ 0) :
    evalExpr env (fastDual x y d) = evalExpr env (mkDualDivExpr x y d) := by
  simp [fastDual, mkDualDivExpr, evalExpr, hd, Int.mul_ediv_cancel]
theorem guardedDual_sound (x y d : PureExpr) (env : Env) :
    evalExpr env (guardedDual x y d) = evalExpr env (mkDualDivExpr x y d) := by
  by_cases hd : evalPure env d = 0
  · simp [guardedDual, evalExpr, evalGuard, hd]
  · simp [guardedDual, evalExpr, evalGuard, hd, fastDual_sound x y d env hd]

/-- Share one residual check across arbitrary pure operands with the same divisor. -/
def topPass (e : Expr) : Expr :=
  match e with
  | .add (.checkedDiv (.pure x) (.pure d₁))
      (.checkedDiv (.mul (.pure y) (.pure d₂)) (.pure d₃)) =>
      if d₁ = d₂ ∧ d₂ = d₃ then guardedDual x y d₁ else e
  | _ => e

theorem topPass_sound (e : Expr) (env : Env) :
    evalExpr env (topPass e) = evalExpr env e := by
  unfold topPass
  split
  · rename_i x d₁ y d₂ d₃
    split
    · rename_i hd
      rcases hd with ⟨h₁₂, h₂₃⟩
      subst d₂
      subst d₃
      exact guardedDual_sound x y d₁ env
    · rfl
  · rfl

/-- Total computable optimizer; rules contain no fixed variable identifiers or benchmark constants. -/
def opt (ctx : GuardIR) (e : Expr) : Expr :=
  if ctx = .top then topPass e else core ctx e

theorem opt_sound (ctx : GuardIR) (e : Expr) (env : Env)
    (hc : evalGuard env ctx = true) : evalExpr env (opt ctx e) = evalExpr env e := by
  unfold opt
  split
  · exact topPass_sound e env
  · exact core_sound ctx e env hc

theorem opt_top_dual (x y d : PureExpr) :
    opt .top (mkDualDivExpr x y d) = guardedDual x y d := by
  simp [opt, topPass, mkDualDivExpr]


theorem core_pure_div (ctx : GuardIR) (num d : PureExpr) (hn : hasNZ ctx d = true) :
    core ctx (.checkedDiv (.pure num) (.pure d)) = .uncheckedDiv (.pure num) (.pure d) := by
  simp [core, smartDiv, hn]

theorem core_cancel_right (ctx : GuardIR) (x d : PureExpr) (hn : hasNZ ctx d = true) :
    core ctx (mkCancelExpr x d) = .pure x := by
  simp [core, smartDiv, mkCancelExpr, hn]

theorem opt_known_dual (x y d : PureExpr) :
    opt (.nonZero d) (mkDualDivExpr x y d) = fastDual x y d := by
  simp [opt, mkDualDivExpr, core, smartDiv, fastDual]

theorem elim_checkedDiv_param (num d : PureExpr) (extra : GuardIR) (env : Env) :
    checkedDivCount (opt (.nonZero d) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    checkedDivCount (opt (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    checkedDivCount (opt (.conj extra (.nonZero d)) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    guardBranchCount (opt (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    execCheckCost env (opt (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 := by
  simp [opt, core_pure_div, checkedDivCount, guardBranchCount, execCheckCost, evalExpr]

theorem known_ctx_elim_param (x y d : PureExpr) (env : Env) :
    checkedDivCount (opt (.nonZero d) (mkDualDivExpr x y d)) = 0 ∧
    guardBranchCount (opt (.nonZero d) (mkDualDivExpr x y d)) = 0 ∧
    execCheckCost env (opt (.nonZero d) (mkDualDivExpr x y d)) = 0 := by
  rw [opt_known_dual]
  by_cases hd : evalPure env d = 0 <;>
    simp [fastDual, checkedDivCount, guardBranchCount, execCheckCost, evalExpr, hd]

theorem unknown_ctx_dedup_param (x y d : PureExpr) (env : Env) (hd : evalPure env d ≠ 0) :
    execCheckCost env (opt .top (mkDualDivExpr x y d)) ≤ 1 ∧
    execCheckCost env (mkDualDivExpr x y d) = 2 := by
  rw [opt_top_dual]
  simp [guardedDual, fastDual, mkDualDivExpr, execCheckCost, guardEvalCost, evalGuard, evalExpr, hd]

theorem zero_div_trap_param (x y d : PureExpr) (env : Env) (hd : evalPure env d = 0) :
    evalExpr env (opt .top (mkDualDivExpr x y d)) = .trap := by
  rw [opt_top_dual]
  simp [guardedDual, mkDualDivExpr, evalExpr, evalGuard, hd]


theorem opt_guarded (ctx : GuardIR) (e : Expr) :
    GuardedEquiv (liftEval evalExpr) (denoteGuard ctx) (opt ctx e) e := by
  intro P hP
  funext env out
  apply propext
  constructor
  · rintro ⟨hp, ho⟩
    exact ⟨hp, (opt_sound ctx e env (hP env hp)).symm.trans ho⟩
  · rintro ⟨hp, ho⟩
    exact ⟨hp, (opt_sound ctx e env (hP env hp)).trans ho⟩

theorem known_ctx_elim (env : Env) :
    checkedDivCount (opt (.nonZero (.var 0)) m1BenchExpr) = 0 ∧
    guardBranchCount (opt (.nonZero (.var 0)) m1BenchExpr) = 0 ∧
    execCheckCost env (opt (.nonZero (.var 0)) m1BenchExpr) = 0 := by
  exact known_ctx_elim_param (.var 1) (.var 2) (.var 0) env
theorem unknown_ctx_dedup (env : Env) (h : env 0 ≠ 0) :
    execCheckCost env (opt .top m1BenchExpr) ≤ 1 ∧ execCheckCost env m1BenchExpr = 2 := by
  exact unknown_ctx_dedup_param (.var 1) (.var 2) (.var 0) env h
theorem zero_div_trap (env : Env) (h : env 0 = 0) :
    evalExpr env (opt .top m1BenchExpr) = .trap := by
  exact zero_div_trap_param (.var 1) (.var 2) (.var 0) env h


theorem core_cancel_left (x d : PureExpr) :
    core (.nonZero d) (.checkedDiv (.mul (.pure d) (.pure x)) (.pure d)) = .pure x := by
  by_cases hx : x = d
  · subst x
    simp [core, smartDiv]
  · simp [core, smartDiv, hx]

theorem cancel_div_param (x d : PureExpr) :
    divOpCount (opt (.nonZero d) (mkCancelExpr x d)) = 0 ∧
    divOpCount (opt (.nonZero d) (.checkedDiv (.mul (.pure d) (.pure x)) (.pure d))) = 0 := by
  simp [opt, core_cancel_right, core_cancel_left, divOpCount]

theorem compositional_binary (d : PureExpr) (e₁ e₂ : Expr)
    (h₁ : checkedDivCount (opt (.nonZero d) e₁) = 0 ∧
      guardBranchCount (opt (.nonZero d) e₁) = 0)
    (h₂ : checkedDivCount (opt (.nonZero d) e₂) = 0 ∧
      guardBranchCount (opt (.nonZero d) e₂) = 0) :
    checkedDivCount (opt (.nonZero d) (.add e₁ e₂)) = 0 ∧
    checkedDivCount (opt (.nonZero d) (.sub e₁ e₂)) = 0 ∧
    checkedDivCount (opt (.nonZero d) (.mul e₁ e₂)) = 0 := by
  simp [opt] at h₁ h₂
  simp [opt, core, checkedDivCount, h₁.1, h₂.1]

theorem cancel_div : divOpCount (opt (.nonZero (.var 0)) m1CancelExpr) = 0 := by
  exact (cancel_div_param (.var 1) (.var 0)).1


/-- Every compiler-dependent obligation in the revised M1 interface, including the original contract. -/
structure UpdatedObligations
    (synthFn : GuardIR → GuardIR → GuardIR) (optFn : GuardIR → Expr → Expr) : Prop where
  original : M1.CompilerObligations synthFn optFn
  topRight : ∀ a, synthFn a .top = .top
  botLeft : ∀ b, synthFn .bot b = .top
  topLeftNZ : ∀ p, synthFn .top (.nonZero p) = .nonZero p
  dischargeLeft : ∀ p rest, synthFn (.conj (.nonZero p) rest) (.nonZero p) = .top
  dischargeRight : ∀ rest p, synthFn (.conj rest (.nonZero p)) (.nonZero p) = .top
  dedupConj : ∀ p, synthFn .top (.conj (.nonZero p) (.nonZero p)) = .nonZero p
  elimParam : ∀ num d extra env,
    checkedDivCount (optFn (.nonZero d) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    checkedDivCount (optFn (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    checkedDivCount (optFn (.conj extra (.nonZero d)) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    guardBranchCount (optFn (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0 ∧
    execCheckCost env (optFn (.conj (.nonZero d) extra) (.checkedDiv (.pure num) (.pure d))) = 0
  cancelParam : ∀ x d,
    divOpCount (optFn (.nonZero d) (mkCancelExpr x d)) = 0 ∧
    divOpCount (optFn (.nonZero d) (.checkedDiv (.mul (.pure d) (.pure x)) (.pure d))) = 0
  compositional : ∀ d e₁ e₂,
    (checkedDivCount (optFn (.nonZero d) e₁) = 0 ∧ guardBranchCount (optFn (.nonZero d) e₁) = 0) →
    (checkedDivCount (optFn (.nonZero d) e₂) = 0 ∧ guardBranchCount (optFn (.nonZero d) e₂) = 0) →
    checkedDivCount (optFn (.nonZero d) (.add e₁ e₂)) = 0 ∧
    checkedDivCount (optFn (.nonZero d) (.sub e₁ e₂)) = 0 ∧
    checkedDivCount (optFn (.nonZero d) (.mul e₁ e₂)) = 0
  knownParam : ∀ x y d env,
    checkedDivCount (optFn (.nonZero d) (mkDualDivExpr x y d)) = 0 ∧
    guardBranchCount (optFn (.nonZero d) (mkDualDivExpr x y d)) = 0 ∧
    execCheckCost env (optFn (.nonZero d) (mkDualDivExpr x y d)) = 0
  dedupParam : ∀ x y d env, evalPure env d ≠ 0 →
    execCheckCost env (optFn .top (mkDualDivExpr x y d)) ≤ 1 ∧
    execCheckCost env (mkDualDivExpr x y d) = 2
  trapParam : ∀ x y d env, evalPure env d = 0 →
    evalExpr env (optFn .top (mkDualDivExpr x y d)) = .trap

theorem original_obligations : M1.CompilerObligations synth opt where
  guardDenote := synth_denote
  universal := synth_universal
  selfDischarge := synth_self
  guarded := opt_guarded
  sound := opt_sound
  known := known_ctx_elim
  cancel := cancel_div
  dedup := unknown_ctx_dedup
  trap := zero_div_trap

theorem all_obligations : UpdatedObligations synth opt where
  original := original_obligations
  topRight := synth_top_right
  botLeft := synth_bot_left
  topLeftNZ := synth_top_left_nonZero
  dischargeLeft := synth_conj_left
  dischargeRight := synth_conj_right
  dedupConj := synth_dedup
  elimParam := elim_checkedDiv_param
  cancelParam := cancel_div_param
  compositional := compositional_binary
  knownParam := known_ctx_elim_param
  dedupParam := unknown_ctx_dedup_param
  trapParam := zero_div_trap_param

theorem updated_obligations_satisfiable :
    ∃ (synthFn : GuardIR → GuardIR → GuardIR) (optFn : GuardIR → Expr → Expr),
      UpdatedObligations synthFn optFn := by
  exact ⟨synth, opt, all_obligations⟩

/-- The old optimizer is rejected independently of which guard synthesizer accompanies it. -/
theorem fixture_optimizer_rejected (synthFn : GuardIR → GuardIR → GuardIR) :
    ¬ UpdatedObligations synthFn M1.opt := by
  intro h
  have bad := (h.knownParam (.var 2) (.var 4) (.var 3) M1.positiveEnv).1
  have two : checkedDivCount (M1.opt (.nonZero (.var 3))
      (mkDualDivExpr (.var 2) (.var 4) (.var 3))) = 2 := by decide
  rw [two] at bad
  cases bad

/-- The old residual wrapper separately fails the new normalization contract. -/
theorem old_synth_rejected (optFn : GuardIR → Expr → Expr) :
    ¬ UpdatedObligations M1.synth optFn := by
  intro h
  have bad := h.topLeftNZ (.var 0)
  change GuardIR.imp .top (.nonZero (.var 0)) = .nonZero (.var 0) at bad
  cases bad

def sampleX : PureExpr := .add (.var 7) (.lit 1)
def sampleY : PureExpr := .mul (.var 9) (.lit 3)
def sampleD : PureExpr := .lit 2
def sampleEnv : Env := fun _ => 4
def sampleExpr : Expr := mkDualDivExpr sampleX sampleY sampleD
def nestedExpr : Expr :=
  .sub (.add (.checkedDiv (.pure sampleX) (.pure sampleD))
    (mkCancelExpr sampleY sampleD)) (.pure (.lit 0))

theorem generalized_positive_witness :
    evalGuard sampleEnv (.nonZero sampleD) = true ∧
    evalExpr sampleEnv sampleExpr = .val 14 ∧
    evalExpr sampleEnv (opt .top sampleExpr) = .val 14 ∧
    execCheckCost sampleEnv sampleExpr = 2 ∧
    execCheckCost sampleEnv (opt .top sampleExpr) = 1 ∧
    checkedDivCount (opt (.nonZero sampleD) nestedExpr) = 0 ∧
    guardBranchCount (opt (.nonZero sampleD) nestedExpr) = 0 ∧
    evalExpr sampleEnv (opt (.nonZero sampleD) nestedExpr) = .val 14 := by
  decide

theorem renamed_reduction :
    checkedDivCount (opt (.nonZero (.var 3)) M1.renamedBench) = 0 ∧
    checkedDivCount (M1.opt (.nonZero (.var 3)) M1.renamedBench) = 2 := by
  decide

theorem normalization_witness :
    synth .top (.nonZero sampleD) = .nonZero sampleD ∧
    synth .top (.conj (.nonZero sampleD) (.nonZero sampleD)) = .nonZero sampleD ∧
    synth (.conj (.eq (.var 8) (.lit 4)) (.nonZero sampleD)) (.nonZero sampleD) = .top := by
  decide

theorem generalized_zero_trap :
    evalExpr sampleEnv (opt .top (mkDualDivExpr sampleX sampleY (.lit 0))) = .trap := by
  decide

end M1R2

end CatSem.RedTeam

/- This check is intentionally outside the semantic namespace: it inspects
   proof dependencies rather than becoming one of the semantic declarations. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, _) =>
    let fromDefs := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]? == some `Specs.Defs
      | none => false
    if (`CatSem.RedTeam).isPrefixOf name || fromDefs then some name else none
  if names.isEmpty then throwError "No audit declarations found"
  for name in names do
    let axioms ← liftCoreM <| Lean.collectAxioms name
    let bad := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
    unless bad.isEmpty do
      throwError m!"Forbidden dependencies for {name}: {bad}"
    if axioms.isEmpty then
      logInfo m!"'{name}' does not depend on any axioms"
    else
      logInfo m!"'{name}' depends on axioms: [{String.intercalate ", " (axioms.toList.map Name.toString)}]"

