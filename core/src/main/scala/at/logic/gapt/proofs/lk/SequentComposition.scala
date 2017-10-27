package at.logic.gapt.proofs.lk

import at.logic.gapt.expr. Expr
import at.logic.gapt.proofs.HOLSequent

trait SequentTerm
class SequentComposition( composedSequents: Vector[SequentTerm]){}


class CLSTerms(proofName:String,CutConfig:HOLSequent, args:Seq[Expr]) extends SequentTerm {}