import LeanDag.RedSnapper.ParallelCertification.Statement
import LeanDag.RedSnapper.TxAgreement.Proof
import LeanDag.RedSnapper.Five.Agreement.Proof

/-!
# Parallel certification — proof

 Conflict safety is reused directly from RS3/RS8.
-/

namespace LeanDag

namespace RedSnapper

namespace ParallelCertification

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]
  {U : Universe Validator BlockId Tx Obj} {A : Anchors U}

private theorem firstIndex_existsUnique {P : ℕ → Prop} (h : ∃ i, P i) :
    ∃! i, FirstIndex P i := by
  classical
  let i := Nat.find h
  have hi : P i := by
    simpa [i] using Nat.find_spec h
  have hleast : ∀ j < i, ¬ P j := by
    intro j hj hp
    exact (Nat.find_min h (by simpa [i] using hj)) hp
  refine ⟨i, ⟨hi, hleast⟩, ?_⟩
  intro j hj
  rcases lt_trichotomy j i with hlt | heq | hgt
  · exact (hleast j hlt hj.1).elim
  · exact heq
  · exact (hj.2 i hgt hi).elim

private theorem three_anchor_exists {V : View U} {tx : Tx} (hmix : T.Mixed tx)
    (h : TxVerdict U A V tx Fate.finalized) :
    ∃ i, MixedFinalAtThree U A tx i := by
  cases h with
  | fastFinal hown hq => exact (hown hmix).elim
  | @finalizeOnCommit i a hi hcand hnc hcert =>
      exact ⟨i, a, hi, Or.inl ⟨hcand, hnc, hcert⟩⟩
  | @resolveCommit i a hi hconf hcand hcert hlive =>
      exact ⟨i, a, hi, Or.inr ⟨hconf, hcand, hcert, hlive⟩⟩

private theorem five_anchor_exists {V : View U} {prio : Tx → Tx → Prop} {tx : Tx}
    (hmix : T.Mixed tx) (h : VerdictFive U A V prio tx Fate.finalized) :
    ∃ j, MixedFinalAtFive U A prio tx j := by
  cases h with
  | fullFinal hown hC hcert => exact (hown hmix).elim
  | finalizeOnCommit hmix' hi hcand hcert =>
      exact ⟨_, _, hi, Or.inl ⟨hcand, hcert⟩⟩
  | recoveryFinal hres hlk hla helig hmin =>
      exact ⟨_, _, hla, Or.inr ⟨_, _, hres, hlk, helig, hmin⟩⟩

private theorem threeMixedSafety : ThreeMixedSafety U A := by
  intro hdisc
  constructor
  · intro V V' tx tx' hmix hmix' hconf htx htx'
    exact TxAgreement.noConflictingFinal hdisc V V' tx tx' htx htx' hconf
  · intro V tx hmix htx
    exact firstIndex_existsUnique (three_anchor_exists hmix htx)

private theorem fiveMixedSafety {prio : Tx → Tx → Prop} : FiveMixedSafety U A prio := by
  intro hord hfive hmove hfd
  constructor
  · intro V V' tx tx' hmix hmix' hconf htx htx'
    exact FiveAgreement.noConflictingFinal hord hfive hmove hfd V V' tx tx' hconf htx htx'
  · intro V tx hmix htx
    exact firstIndex_existsUnique (five_anchor_exists hmix htx)

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _ _ U A
  exact ⟨threeMixedSafety, fun prio => fiveMixedSafety⟩

end ParallelCertification

end RedSnapper

end LeanDag
