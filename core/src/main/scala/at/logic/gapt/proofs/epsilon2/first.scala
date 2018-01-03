package at.logic.gapt.proofs.epsilon2

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.SkolemFunctions
import at.logic.gapt.proofs.Context

object reduceEpsilons {

  def replace( cfs: Vector[CriticalFormula], what: Expr, bys: Iterable[Expr] ): Vector[CriticalFormula] =
    ( cfs.toSet ++ bys.view.flatMap( by => TermReplacement( cfs, Map( what -> by ) ) ) ).toVector

  def reduce1( cfs: Vector[CriticalFormula], skSym: Const ): Option[Vector[CriticalFormula]] = {
    val cfsForSkSym = cfs.filter( _.skSym == skSym )
    if ( cfsForSkSym.isEmpty ) None else Some {
      val skTerms = cfsForSkSym.map( _.skTerm ).toSet
      val argSubTerms = skTerms.flatMap { case Apps( _, args ) => args }
      val maximal = skTerms.diff( argSubTerms ).head
      val ( maximalCFs, rest ) = cfs.partition( _.skTerm == maximal )
      replace( rest, maximal, maximalCFs.map( _.term ) )
    }
  }

  def reduceSkSym( cfs: Vector[CriticalFormula], skSym: Const ): Vector[CriticalFormula] =
    reduce1( cfs, skSym ) match {
      case Some( next ) => reduceSkSym( next, skSym )
      case None         => cfs
    }

  def apply( p: EpsilonProof )( implicit ctx: Context ): EpsilonProof = {
    var cfs = p.criticalFormulas
    val occursInEpsilonization = constants( p.epsilonized )
    for {
      skSym <- ctx.get[SkolemFunctions].dependencyOrder
      if !occursInEpsilonization( skSym )
    } cfs = reduceSkSym( cfs, skSym )
    p.copy( criticalFormulas = cfs )
  }

}