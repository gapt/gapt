package gapt.proofs.lk

import gapt.expr.Formula
import gapt.proofs.ContextRule

trait CommonRule extends LKProof with ContextRule[Formula, LKProof]
