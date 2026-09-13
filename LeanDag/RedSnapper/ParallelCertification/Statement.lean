import LeanDag.RedSnapper.Model.Five.Verdict
import LeanDag.RedSnapper.Model.Five.Moves

/-!
# Parallel certification — statement

-/

namespace LeanDag

namespace RedSnapper

namespace ParallelCertification

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]

/-- `i` is the first natural-number index satisfying `P`. -/
def FirstIndex (P : ℕ → Prop) (i : ℕ) : Prop :=
  P i ∧ ∀ j < i, ¬ P j

/-- A committed anchor at index `i` can finalise the mixed transaction
`tx` in the `3f+1` protocol. -/
def MixedFinalAtThree (U : Universe Validator BlockId Tx Obj) (A : Anchors U)
    (tx : Tx) (i : ℕ) : Prop :=
  ∃ a, A.seq[i]? = some a ∧
    ((IsCandidate U a (T.input tx) tx ∧
        ¬ Conflicted U a (T.input tx) ∧ HasCert U a tx) ∨
      (Conflicted U a (T.input tx) ∧
        IsCandidate U a (T.input tx) tx ∧ HasCert U a tx ∧ ¬ DeadAt U A i tx))

/-- A committed anchor at index `j` can finalise the mixed transaction
`tx` in the `5f+1` protocol. The first disjunct is
`FinalizeOnCommitTX`; the second is the deterministic recovery winner. -/
def MixedFinalAtFive (U : Universe Validator BlockId Tx Obj) (A : Anchors U)
    (prio : Tx → Tx → Prop) (tx : Tx) (j : ℕ) : Prop :=
  ∃ a, A.seq[j]? = some a ∧
    ((IsCandidate U a (T.input tx) tx ∧
        ∃ C ∈ U.ids, Reaches U a C ∧ IsFullCert U C tx) ∨
      ∃ i aₖ, ResolvesFiveAt U A (T.input tx) i j ∧
        A.seq[i]? = some aₖ ∧ EligibleFive U aₖ a (T.input tx) tx ∧
        ∀ tx', EligibleFive U aₖ a (T.input tx) tx' → prio tx tx')

/-- The new mixed-object safety statement for the `3f+1` protocol:
conflicting mixed transactions never both finalise, and every finalised
mixed transaction has a unique first committed anchor at which its
anchor-finality condition holds. -/
def ThreeMixedSafety (U : Universe Validator BlockId Tx Obj) (A : Anchors U) : Prop :=
  StanceDiscipline U →
    (∀ (V V' : View U) (tx tx' : Tx), T.Mixed tx → T.Mixed tx' → Conflict tx tx' →
      TxVerdict U A V tx Fate.finalized → TxVerdict U A V' tx' Fate.finalized → False) ∧
    ∀ (V : View U) (tx : Tx), T.Mixed tx → TxVerdict U A V tx Fate.finalized →
      ∃! i, FirstIndex (MixedFinalAtThree U A tx) i

/-- The new mixed-object safety statement for the `5f+1` protocol:
conflicting mixed transactions never both finalise, and every finalised
mixed transaction has a unique first committed anchor at which its
anchor-finality condition holds. -/
def FiveMixedSafety (U : Universe Validator BlockId Tx Obj) (A : Anchors U)
    (prio : Tx → Tx → Prop) : Prop :=
  IsLinearOrder Tx prio → Five Validator → MoveDiscipline U → FreezeDiscipline U →
    (∀ (V V' : View U) (tx tx' : Tx), T.Mixed tx → T.Mixed tx' → Conflict tx tx' →
      VerdictFive U A V prio tx Fate.finalized →
      VerdictFive U A V' prio tx' Fate.finalized → False) ∧
    ∀ (V : View U) (tx : Tx), T.Mixed tx →
      VerdictFive U A V prio tx Fate.finalized →
      ∃! j, FirstIndex (MixedFinalAtFive U A prio tx) j

/-- Parallel-certification mixed safety for both committee sizes. -/
def Statement : Prop :=
  ∀ (Validator BlockId Tx Obj : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] [Faults Validator] [Transactions Tx Obj]
    (U : Universe Validator BlockId Tx Obj) (A : Anchors U),
    ThreeMixedSafety U A ∧ ∀ prio : Tx → Tx → Prop, FiveMixedSafety U A prio

end ParallelCertification

end RedSnapper

end LeanDag
