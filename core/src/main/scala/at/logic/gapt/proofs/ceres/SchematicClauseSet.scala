package at.logic.gapt.proofs.ceres

import java.lang.Iterable

import at.logic.gapt.expr.{Atom, Expr}
import at.logic.gapt.proofs.Context.ProofDefinitions
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{Context, HOLSequent, SetSequent}

//Idea behind type, for each proof symbol we have a pair of Maps, that is basecase
// and step case, which for each configuration has a set of sequents over atoms
//representing the clauses.
object SchematicClauseSet {
  def apply( TopSym:String,
             ctx:Context,
             cutConfig:HOLSequent = HOLSequent()  ):
  Option[Map[String, Set[Map[HOLSequent,Set[(Expr,SetSequent[Atom])]]]]] = {
    val SchematicClauseSetRet = Map[String, Set[Map[HOLSequent,Set[(Expr,SetSequent[Atom])]]]]()
    val ProofNames = ctx.get[ProofDefinitions].components.keySet
    if(ProofNames.contains(TopSym)) {
      val TopProofs = ctx.get[ProofDefinitions].components.get(TopSym) match {
        case Some(w) => w
        case None => Set[(Expr, LKProof)]()
      }
      //Makes the Structs for the top proofs
      val TopStructs: Set[(Expr, Struct[Nothing])] = TopProofs.map(x => {
        val (ex, lp) = x
        (ex, StructCreators.extract(lp, ProofNames))
      })
      //For each Struct we will find the proof links that the Struct is dependent on.
      val TopDependents: Set[(String, HOLSequent)] = TopStructs.fold(Set[(String, HOLSequent)]())((w, e) => {
        val (ex, st:Struct[Nothing]) = e
        val temp = SchematicLeafs(st)
        val CLSyms: Set[(String, HOLSequent)] = temp.fold(Set[(String, HOLSequent)]())((y, a) => {
          val CLS(pf, ccon, frv, l) = a
          if (pf.matches(TopSym) && ccon.equals(cutConfig)) (pf, ccon)
          else y.asInstanceOf[Set[(String, HOLSequent)]] ++ Set[(String, HOLSequent)]((pf, ccon))
        }).asInstanceOf[Set[(String, HOLSequent)]]
         w.asInstanceOf[Set[(String, HOLSequent)]] ++ CLSyms
      }).asInstanceOf[Set[(String, HOLSequent)]]
      //the constructions from all the dependents
      val DependentMaps:Map[String, Set[Map[HOLSequent, Set[(Expr, SetSequent[Atom])]]]]= TopDependents.map(x => {
        val (sym, ccon) = x
        SchematicClauseSet(sym, ctx, ccon)
      }).fold(Map[String, Set[Map[HOLSequent, Set[(Expr, SetSequent[Atom])]]]]())((x,y) => {
        x.asInstanceOf[Map[String, Set[Map[HOLSequent, Set[(Expr, SetSequent[Atom])]]]]]++y.asInstanceOf[Map[String, Set[Map[HOLSequent, Set[(Expr, SetSequent[Atom])]]]]]
      }).asInstanceOf[Map[String, Set[Map[HOLSequent, Set[(Expr, SetSequent[Atom])]]]]]

      //The top constructions
      val TopClauses: Map[HOLSequent, Set[(Expr, SetSequent[Atom])]] = TopStructs.map(x => {
        val (ex, st) = x
        (cutConfig, ex, CharacteristicClauseSet(st))
      }).asInstanceOf[Map[HOLSequent, Set[(Expr, SetSequent[Atom])]]]
      val FinalMap:Map[String, Set[Map[HOLSequent, Set[(Expr, SetSequent[Atom])]]]] = DependentMaps ++ Map[String, Set[Map[HOLSequent, Set[(Expr, SetSequent[Atom])]]]]((TopSym, Set[Map[HOLSequent, Set[(Expr, SetSequent[Atom])]]](TopClauses)))
      Some(FinalMap)
    }
    else None
  }
}
