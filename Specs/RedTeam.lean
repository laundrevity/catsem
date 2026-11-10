import Specs.Target
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Guard-synthesis specification audit

`synthesizeGuard_sound` matches its blueprint claim after unfolding
`synthesizeGuard`. `synthesizeGuard_weakest` states only the forward direction
of the blueprint's iff. Its reverse follows from soundness and monotonicity
of meet, so the pair entails the full claim, but the named statement alone
does not state the whole equivalence. `blueprint_adjunction` checks the iff
independently below.

Both declarations in `Specs.Target` currently have placeholder proofs. None
of the proofs below invokes them: importing a placeholder must not turn an
audit into circular evidence. The Bool cases use kernel-checked `decide`;
the Prop proofs use conjunction and implication directly. Axiom inspection
should therefore find no `sorryAx` in these audit declarations.

Bool exhausts four state/target pairs and eight state/target/guard triples.
Prop checks arbitrary propositions, including all True/False combinations.
The explicit active witnesses show that the hypotheses are satisfiable with
a true state and a true guard. The rejected witnesses show that the validity
premise is meaningful and cannot simply be omitted.
-/

namespace CatSem.RedTeam

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

/-- Also check the direction omitted from the named weakest-guard target. -/
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

end CatSem.RedTeam
