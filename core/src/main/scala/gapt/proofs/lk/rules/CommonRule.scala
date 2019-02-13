package gapt.proofs.lk.rules

import gapt.expr.Formula
import gapt.proofs.ContextRule
import gapt.proofs.lk.LKProof

trait CommonRule extends LKProof with ContextRule[Formula, LKProof]
