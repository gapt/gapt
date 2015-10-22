package at.logic.gapt.proofs.ceres.clauseSchema

import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.occurrences.{ defaultFormulaOccurrenceFactory, FormulaOccurrence }
import at.logic.gapt.proofs.shlk.AndEquivalenceRule1._
import at.logic.gapt.proofs.shlk._
import at.logic.gapt.expr.schema.{ SchemaSubstitution => SchemaSubstitution, _ }
import at.logic.gapt.expr._
import at.logic.gapt.expr.BetaReduction._
import at.logic.gapt.proofs.shlk.printSchemaProof

abstract class sResolutionTerm {}
abstract class sClauseTerm extends sResolutionTerm {}
abstract class sClause extends sClauseTerm {
  override def toString: String
}

// c(k+1, x, X)
class clauseSchema( val name: String, val args: List[Object] ) extends sClause {
  override def toString: String = name + "(" + args.head.toString + { args.tail.foldRight( "" )( ( x, rez ) => ", " + x.toString + rez ) } + ")"
}
object clauseSchema {
  def apply( sym: String, l: List[Object] ): clauseSchema = {
    new clauseSchema( sym, l )
  }
  def unapply( c: sClause ) = c match {
    case sc: clauseSchema => Some( ( sc.name, sc.args ) )
    case _                => None
  }
}

//  X
class sClauseVar( val name: String ) extends sClause {
  override def toString = this.name
  override def equals( a: Any ): Boolean = a match {
    case v: sClauseVar if this.name == v.name => true
    case _                                    => false
  }
}
object sClauseVar {
  def apply( name: String ): sClauseVar = new sClauseVar( name )
  def unaply( s: sClause ) = s match {
    case v: sClauseVar => Some( v.name )
    case _             => None
  }
}

//usual clause : no schematic symbols and no schematic variables
class nonVarSclause( val ant: List[SchemaFormula], val succ: List[SchemaFormula] ) extends sClause {
  override def toString = {
    printSchemaProof.sequentToString( OccSequent( ant.map( f => defaultFormulaOccurrenceFactory.createFormulaOccurrence( f, List() ) ), succ.map( f => defaultFormulaOccurrenceFactory.createFormulaOccurrence( f, List() ) ) ) )
    //    ant + " |- " + succ
  }
  override def equals( a: Any ) = a match {
    case non: nonVarSclause => this.ant.toSet == non.ant.toSet && this.succ.toSet == non.succ.toSet
    case _                  => false
  }
}
object nonVarSclause {
  def apply( ant1: List[SchemaFormula], succ1: List[SchemaFormula] ): nonVarSclause = {
    new nonVarSclause( ant1, succ1 )
  }
  def unapply( c: sClause ) = c match {
    case non: nonVarSclause => Some( non.ant, non.succ )
    case _                  => None
  }
}

// sClause1 ◦ sClause2
class sClauseComposition( val sclause1: sClause, val sclause2: sClause ) extends sClause {
  override def toString = { sclause1 + " ◦ " + sclause2 }
}
object sClauseComposition {
  def apply( scl1: sClause, scl2: sClause ): sClause = new sClauseComposition( scl1, scl2 )
  def unaply( s: sClause ) = s match {
    case compos: sClauseComposition => Some( Tuple2( compos.sclause1, compos.sclause2 ) )
    case _                          => None
  }
}

//makes it with only one  "⊢" sign, i.e. removes ◦ as possible
object deComposeSClause {
  def apply( c: sClause ): sClause = {
    val mergeNonVarSClauses = {
      val res = getNonVarSclauses( c )
      if ( res.length == 1 )
        res.head
      else
        res.tail.foldLeft( res.head )( ( acc, clause ) => nonVarSclause( acc.asInstanceOf[nonVarSclause].ant ++ clause.asInstanceOf[nonVarSclause].ant, acc.asInstanceOf[nonVarSclause].succ ++ clause.asInstanceOf[nonVarSclause].succ ) ).asInstanceOf[sClause]
    }
    val sClauseVars = getSClausVars( c )
    if ( sClauseVars.isEmpty )
      return mergeNonVarSClauses.asInstanceOf[nonVarSclause]
    sClauseVars.foldLeft( mergeNonVarSClauses.asInstanceOf[sClause] )( ( acc, v ) => sClauseComposition( acc, v ) ).asInstanceOf[sClauseComposition]
  }
  def getNonVarSclauses( c: sClause ): List[sClause] = c match {
    case v: sClauseVar      => List.empty[sClause]
    case non: nonVarSclause => non :: Nil
    case comp: sClauseComposition =>
      getNonVarSclauses( comp.sclause1 ) ++ getNonVarSclauses( comp.sclause2 )
    case _ => {
      throw new Exception( "Error in getNonVarSclauses!" )
    }
  }
  private def getSClausVars( c: sClause ): List[sClause] = c match {
    case v: sClauseVar      => v :: Nil
    case non: nonVarSclause => List.empty[sClause]
    case comp: sClauseComposition =>
      getSClausVars( comp.sclause1 ) ++ getSClausVars( comp.sclause2 )
  }
}

//replace "v" with the sClause from the Map
object replace {
  val nLine = sys.props( "line.separator" )
  def apply( c: sClause, varList: Map[sClauseVar, sClause] ): sClause = c match {
    case v: sClauseVar if varList.keySet.contains( v )  => varList.get( v ).get
    case v: sClauseVar if !varList.keySet.contains( v ) => throw new Exception( nLine + "ERROR 112" + nLine + "!" )
    case non: nonVarSclause                             => c
    case comp: sClauseComposition =>
      sClauseComposition( apply( comp.sclause1, varList ), apply( comp.sclause2, varList ) )
  }
}

//applies sub to a sClauseTerm or sClause
//the sub is of type Var -> SchemaExpression
object applySubToSclauseOrSclauseTerm {
  val nLine = sys.props( "line.separator" )
  def apply( sub: SchemaSubstitution, c: sClauseTerm ): sClauseTerm = {
    c match {
      case v: sClauseVar => c
      case cs: clauseSetTerm => {
        clauseSetTerm( cs.name, cs.args.map( x => {
          x match {
            case e: SchemaExpression => sub( x.asInstanceOf[SchemaExpression] )
            case _                   => x
          }
        } ) )
      }
      case non: nonVarSclause => {
        val ant1 = non.ant.map( f => sub( f ) )
        val succ1 = non.succ.map( f => sub( f ) )
        nonVarSclause( ant1, succ1 )
      }
      case compos: sClauseComposition => {
        sClauseComposition( apply( sub, compos.sclause1 ).asInstanceOf[sClause], apply( sub, compos.sclause2 ).asInstanceOf[sClause] )
      }
      case cs: clauseSchema => {
        clauseSchema( cs.name, cs.args.map( x => {
          x match {
            case e: SchemaExpression => sub( x.asInstanceOf[SchemaExpression] )
            case _                   => x
          }
        } ) )
      }
      case t: sclTimes   => sclTimes( apply( sub, t.left ), apply( sub, t.right ) )
      case t: sclPlus    => sclPlus( apply( sub, t.left ), apply( sub, t.right ) )
      case t: sclTermVar => t
      case _             => throw new Exception( nLine + "ERROR in applySubToSclauseOrSclauseTerm ! " + nLine )
    }
  }
}

// σ(k+1, x, l)
object sTermN {
  val nLine = sys.props( "line.separator" )
  //the l.head should be of type Tindex() !
  def apply( f: String, l: List[SchemaExpression] ): SchemaExpression = {
    require( l.head.exptype == Tindex )
    val typ = l.map( x => x.exptype ).foldRight( Ti.asInstanceOf[Ty] )( ( x, t ) => x -> t )
    val func = Const( f, typ )
    return SchemaFunction( func, l )
  }
  def apply( f: Const, i: IntegerTerm, l: List[SchemaExpression] ): SchemaExpression = {
    SchemaFunction( f, l )
  }
  def unapply( s: SchemaExpression ) = s match {
    case SchemaFunction( name: Const, args, typ ) if typ == Ti && args.length != 0 && args.head.exptype == Tindex => {
      val typ = args.map( x => x.exptype ).foldLeft( Ti.asInstanceOf[Ty] )( ( x, t ) => x -> t )
      val f = Const( name.name, typ )
      Some( ( f.name.toString(), args.head.asInstanceOf[SchemaExpression], args.tail.asInstanceOf[List[SchemaExpression]] ) )
    }
    case _ => None
  }
}

// dbTRS for σ(k+1, x, l), i.e. sTermN
class dbTRSsTermN( val map: Map[String, Tuple2[Tuple2[SchemaExpression, SchemaExpression], Tuple2[SchemaExpression, SchemaExpression]]] ) {
  val nLine = sys.props( "line.separator" )

  def add( term: String, base: Tuple2[SchemaExpression, SchemaExpression], step: Tuple2[SchemaExpression, SchemaExpression] ): dbTRSsTermN = {
    val newMap = map + Tuple2( term, Tuple2( base, step ) )
    return new dbTRSsTermN( newMap )
  }
  override def toString() = map.keySet.foldLeft( nLine + nLine )( ( acc, s ) => map.get( s ).get._1._1 + "  →  " + map.get( s ).get._1._2 + nLine + map.get( s ).get._2._1 + "  →  " + map.get( s ).get._2._2 + nLine + nLine + acc )
}
object dbTRSsTermN {
  def apply( term: String, base: Tuple2[SchemaExpression, SchemaExpression], step: Tuple2[SchemaExpression, SchemaExpression] ): dbTRSsTermN = {
    val m = Map.empty[String, Tuple2[Tuple2[SchemaExpression, SchemaExpression], Tuple2[SchemaExpression, SchemaExpression]]] + Tuple2( term, Tuple2( base, step ) )
    new dbTRSsTermN( m )
  }
  def apply() = new dbTRSsTermN( Map.empty[String, Tuple2[Tuple2[SchemaExpression, SchemaExpression], Tuple2[SchemaExpression, SchemaExpression]]] )
}

// dbTRS for c(k+1, x, X)clauseSchema
class dbTRSclauseSchema( val map: Map[String, Tuple2[Tuple2[sClause, sClause], Tuple2[sClause, sClause]]] ) {
  override def toString() = map.keySet.foldLeft( "" )( ( acc, s ) => map.get( s ).get._1._1 + "  →  " + map.get( s ).get._1._2 + sys.props( "line.separator" ) + map.get( s ).get._2._1 + "  →  " + map.get( s ).get._2._2 + acc )
}
object dbTRSclauseSchema {
  def apply( term: String, base: Tuple2[sClause, sClause], step: Tuple2[sClause, sClause] ): dbTRSclauseSchema = {
    val m = Map.empty[String, Tuple2[Tuple2[sClause, sClause], Tuple2[sClause, sClause]]] + Tuple2( term, Tuple2( base, step ) )
    new dbTRSclauseSchema( m )
  }
  def apply() = new dbTRSclauseSchema( Map.empty[String, Tuple2[Tuple2[sClause, sClause], Tuple2[sClause, sClause]]] )
}

// unfolds terms of the form : σ(k+1, x, l)
//k : IntVar, x: Var of type ind->i, l: IntVar
object unfoldSTermN {
  //for ground term
  def apply( t: SchemaExpression, trs: dbTRSsTermN ): SchemaExpression = {
    val k = IntVar( "k" )
    val l = IntVar( "l" )
    t match {
      case sTermN( func, i, arg ) if trs.map.contains( func ) => {
        if ( i == IntZero() ) {
          val map = if ( arg.size != 0 )
            Map[Var, SchemaExpression]() + Tuple2( k, i ) + Tuple2( l, arg.last )
          else
            Map[Var, SchemaExpression]() + Tuple2( k, i )
          val subst = SchemaSubstitution( map )
          val base = trs.map.get( func ).get._1._2
          subst( base )
        } else if ( i == k ) t
        else {
          val map = if ( arg.size != 0 )
            Map[Var, SchemaExpression]() + Tuple2( k, i ) + Tuple2( l, arg.last )
          else
            Map[Var, SchemaExpression]() + Tuple2( k, i )
          val subst = SchemaSubstitution( map )
          trs.map.get( func ).get._2._2 match {
            case foTerm( name, arg1 ) => foTerm( name, apply( sTermN( func, Pred( i.asInstanceOf[IntegerTerm] ) :: ( arg.map( x => subst( x ) ) ) ), trs ) :: Nil )
          }
        }
      }
      case _ => t
    }
  }
}

// rewrites  σ(k+1, x, k)  in  P(σ(k+1, x, k))
object unfoldGroundAtom {
  def apply( f: SchemaFormula, trs: dbTRSsTermN ): SchemaFormula = f match {
    case SchemaAtom( name: Var, args )   => SchemaAtom( name, args.map( x => unfoldSTermN( x, trs ) ) )
    case SchemaAtom( name: Const, args ) => SchemaAtom( name, args.map( x => unfoldSTermN( x, trs ) ) )
    case _                               => f
  }
  def apply( f: SchemaFormula ): SchemaFormula = f match {
    case SchemaAtom( name: Var, args )   => SchemaAtom( name, args.map( x => unfoldSTerm( x ) ) )
    case SchemaAtom( name: Const, args ) => SchemaAtom( name, args.map( x => unfoldSTerm( x ) ) )
    case _                               => f
  }
}

//c(3, x, X) is unfolded
object unfoldSchemaClause {
  def apply( t: sClause, trsSclause: dbTRSclauseSchema, trsSterms: dbTRSsTermN, subst: SchemaSubstitution ): sClause = {
    val k = IntVar( "k" )
    t match {
      case clauseSchema( func, i :: arg ) if trsSclause.map.contains( func ) => {
        if ( i == IntZero() ) {
          val base = trsSclause.map.get( func ).get._1._2
          unfoldSchemaClause( base, trsSclause, trsSterms, subst ) //subst(base)
        } else if ( i == k )
          t
        else {
          apply( trsSclause.map.get( func ).get._2._2, trsSclause, trsSterms, subst )
        }
      }
      case nonVarSclause( ant, succ ) => {
        val newant = ant.map( x => subst( x ).asInstanceOf[SchemaFormula] )
        val newsucc = succ.map( x => subst( x ).asInstanceOf[SchemaFormula] )
        nonVarSclause( newant.map( x => unfoldGroundAtom( x, trsSterms ) ), newsucc.map( x => unfoldGroundAtom( x, trsSterms ) ) )
      }
      case co: sClauseComposition => {
        val k = IntVar( "k" )
        val map =
          if ( subst.schemamap.get( k ).get.asInstanceOf[IntegerTerm] == IntZero() )
            subst.schemamap
          else {
            ( subst.schemamap - k ) + Tuple2( k, Pred( subst.schemamap.get( k ).get.asInstanceOf[IntegerTerm] ) )
          }
        val new_subst = SchemaSubstitution( map )
        val l = apply( applySubToSclauseOrSclauseTerm( subst, co.sclause1 ).asInstanceOf[sClause], trsSclause, trsSterms, new_subst )
        val r = apply( applySubToSclauseOrSclauseTerm( subst, co.sclause2 ).asInstanceOf[sClause], trsSclause, trsSterms, new_subst )
        sClauseComposition( l, r )
      }
      case _ => t
    }
  }
}

// d(k+1, x, X) -> sClauseTerm ⊗/⊕ sClauseTerm
class clauseSetTerm( val name: String, val args: List[Object] ) extends sClauseTerm {
  override def toString: String = name + "(" + args.head.toString + { args.tail.foldRight( "" )( ( x, rez ) => ", " + x.toString + rez ) } + ")"
}
object clauseSetTerm {
  def apply( sym: String, l: List[Object] ): clauseSetTerm = {
    new clauseSetTerm( sym, l )
  }
  def unapply( c: sClauseTerm ) = c match {
    case sc: clauseSetTerm => Some( ( sc.name, sc.args ) )
    case _                 => None
  }
}

//clause schema term ⊕
class sclPlus( val left: sClauseTerm, val right: sClauseTerm ) extends sClauseTerm {
  override def toString() = "(" + left.toString + " ⊕ " + right.toString + ")"
}
object sclPlus {
  def apply( l: sClauseTerm, r: sClauseTerm ): sclPlus = {
    new sclPlus( l, r )
  }
  def unapply( t: sClauseTerm ) = t match {
    case s: sclPlus => Some( ( s.left, s.right ) )
    case _          => None
  }
}

//clause schema term ⊗
class sclTimes( val left: sClauseTerm, var right: sClauseTerm ) extends sClauseTerm {
  override def toString() = " ( " + left.toString + " ⊗ " + right.toString + " ) "
}
object sclTimes {
  def apply( l: sClauseTerm, r: sClauseTerm ): sclTimes = {
    new sclTimes( l, r )
  }
  def unapply( t: sClauseTerm ) = t match {
    case s: sclTimes => Some( ( s.left, s.right ) )
    case _           => None
  }
}

//clause schema term variable ξ
class sclTermVar( val name: String ) extends sClauseTerm {
  override def toString() = name
}
object sclTermVar {
  def apply( name: String ): sclTermVar = {
    new sclTermVar( name )
  }
  def unapply( t: sClauseTerm ) = t match {
    case s: sclTermVar => Some( ( s.name ) )
    case _             => None
  }
}

//unfolds a ground schema clause term
object unfoldSclauseTerm {
  def apply( t: sClauseTerm, trsSclause: dbTRSclauseSchema, trsSterms: dbTRSsTermN, subst: SchemaSubstitution ): sClauseTerm = {
    t match {
      case x: sclTermVar => t
      case s: sClause    => unfoldSchemaClause( s, trsSclause, trsSterms, subst )
      case x: sclTimes   => sclTimes( apply( x.left, trsSclause, trsSterms, subst ), apply( x.right, trsSclause, trsSterms, subst ) )
      case x: sclPlus    => sclPlus( apply( x.left, trsSclause, trsSterms, subst ), apply( x.right, trsSclause, trsSterms, subst ) )
      case _             => throw new Exception( "case _ => in object unfoldSclauseTerm" )
    }
  }
}

//substitution for X in the clause schema c(k+1, x, X)
class sClauseVarSubstitution( val map: Map[sClauseVar, nonVarSclause] ) {
  def apply( c: sClause ): sClause = {
    c match {
      case v: sClauseVar if map.contains( v ) => map.get( v ).get
      case non: nonVarSclause                 => non
      case cls: clauseSchema => clauseSchema( cls.name, cls.args.map( x => {
        if ( x.isInstanceOf[sClauseVar] )
          apply( x.asInstanceOf[sClause] )
        else
          x
      } ) )
      case _ => c
    }
  }
}

// substitution for ξ
class sclTermVarSubstitution( val map: Map[sclTermVar, clauseSchema] ) {
  def apply( sclTerm: sClauseTerm ): sClauseTerm = {
    sclTerm match {
      case t: sclTermVar if map.contains( t ) => map.get( t ).get
      case t: sclTimes                        => sclTimes( apply( t.left ), apply( t.right ) )
      case t: sclPlus                         => sclPlus( apply( t.left ), apply( t.right ) )
      case _                                  => sclTerm
    }
  }
}

class dbTRSclauseSetTerm( var map: Map[String, Tuple2[Tuple2[sClauseTerm, sClauseTerm], Tuple2[sClauseTerm, sClauseTerm]]] ) {
  def add( term: String, base: Tuple2[sClauseTerm, sClauseTerm], step: Tuple2[sClauseTerm, sClauseTerm] ): Unit = {
    val newMap = map + Tuple2( term, Tuple2( base, step ) )
    map = newMap
  }
  override def toString() = map.keySet.foldLeft( "" )( ( acc, s ) => map.get( s ).get._1._1 + "  →  " + map.get( s ).get._1._2 + sys.props( "line.separator" ) + map.get( s ).get._2._1 + "  →  " + map.get( s ).get._2._2 + acc )
}
//the t.r.s. for the clause schema
object dbTRSclauseSetTerm {
  def apply( term: String, base: Tuple2[sClauseTerm, sClauseTerm], step: Tuple2[sClauseTerm, sClauseTerm] ): dbTRSclauseSetTerm = {
    val m = Map.empty[String, Tuple2[Tuple2[sClauseTerm, sClauseTerm], Tuple2[sClauseTerm, sClauseTerm]]] + Tuple2( term, Tuple2( base, step ) )
    new dbTRSclauseSetTerm( m )
  }
  def apply() = new dbTRSclauseSetTerm( Map.empty[String, Tuple2[Tuple2[sClauseTerm, sClauseTerm], Tuple2[sClauseTerm, sClauseTerm]]] )
}

// ---------    resolution schemata ------------------

//r(c(k+1, x, X); P(x(k))⊢; P(x(k)))
class rTerm( val left: sResolutionTerm, val right: sResolutionTerm, val atom: SchemaFormula ) extends sResolutionTerm {
  override def toString() = "r( " + left.toString + " ; " + right.toString + " ; " + atom.toString + " )"
}
object rTerm {
  def apply( l: sResolutionTerm, r: sResolutionTerm, at: SchemaFormula ): rTerm = {
    require( at match {
      case SchemaAtom( _, _ ) => true
      case _                  => false
    } )
    new rTerm( l, r, at )
  }
  def unapply( r: sResolutionTerm ) = r match {
    case rt: rTerm => Some( ( rt.left, rt.right, rt.atom ) )
    case _         => None
  }
}

//grounded rTerm
object resolutionDeduction {
  def apply( t: sResolutionTerm, trsSclause: dbTRSclauseSchema, trsSterms: dbTRSsTermN, subst: SchemaSubstitution, mapX: Map[sClauseVar, sClause] ): sResolutionTerm = {
    t match {
      case non: nonVarSclause => non
      case r: rTerm => {
        if ( r.left.isInstanceOf[nonVarSclause]
          && r.right.isInstanceOf[nonVarSclause]
          && r.left.asInstanceOf[nonVarSclause].succ.contains( r.atom )
          && r.right.asInstanceOf[nonVarSclause].ant.contains( r.atom ) ) {
          val non2Ant = r.right.asInstanceOf[nonVarSclause].ant.filter( f => f != r.atom )
          val non1Succ = r.left.asInstanceOf[nonVarSclause].succ.filter( f => f != r.atom )
          return nonVarSclause( r.left.asInstanceOf[nonVarSclause].ant ::: non2Ant, r.right.asInstanceOf[nonVarSclause].succ ::: non1Succ )
        } else {
          val left = apply( r.left, trsSclause, trsSterms, subst, mapX )
          val right = apply( r.right, trsSclause, trsSterms, subst, mapX )
          apply( rTerm( left, right, r.atom ), trsSclause, trsSterms, subst, mapX )
        }
      }
      case c: clauseSchema => deComposeSClause( replace( unfoldSchemaClause( c, trsSclause, trsSterms, subst ), mapX ) )
      case _ => {
        println( sys.props( "line.separator" ) + " case _ => in resolutionDeduction 2 : " + t )
        t
      }
    }
  }
}

//ρ(k+1, x, X) , where X is a sClauseVar ; x is a fo2Var
class ResolutionProofSchema( val name: String, val args: List[Object] ) extends sResolutionTerm {
  override def toString() = name + "(" + args.head.toString + { args.tail.foldRight( "" )( ( x, rez ) => ", " + x.toString + rez ) } + ")"
}
object ResolutionProofSchema {
  def apply( name: String, args: List[Object] ): ResolutionProofSchema = {
    new ResolutionProofSchema( name, args )
  }
  def unapply( rs: sResolutionTerm ) = rs match {
    case r: ResolutionProofSchema => Some( ( r.name, r.args ) )
    case _                        => None
  }
}

//the t.r.s. for the resolution schema (global object)
object resolutionProofSchemaDB extends Iterable[( String, Tuple2[Tuple2[sResolutionTerm, sResolutionTerm], Tuple2[sResolutionTerm, sResolutionTerm]] )] with TraversableOnce[( String, Tuple2[Tuple2[sResolutionTerm, sResolutionTerm], Tuple2[sResolutionTerm, sResolutionTerm]] )] {
  val map = new scala.collection.mutable.HashMap[String, Tuple2[Tuple2[sResolutionTerm, sResolutionTerm], Tuple2[sResolutionTerm, sResolutionTerm]]]
  def get( name: String ) = map( name )
  def clear = map.clear
  def add( term: String, base: Tuple2[sResolutionTerm, sResolutionTerm], step: Tuple2[sResolutionTerm, sResolutionTerm] ) = {
    map.put( term, Tuple2( base, step ) )
  }
  override def toString() = map.keySet.foldLeft( "" )( ( acc, s ) => map.get( s ).get._1._1 + "  →  " + map.get( s ).get._1._2 + sys.props( "line.separator" ) + map.get( s ).get._2._1 + "  →  " + map.get( s ).get._2._2 + acc )
  def iterator = map.iterator
}

//substitute a variable of type ω in a resolution term
object IntVarSubstitution {
  def apply( r: sResolutionTerm, subst: SchemaSubstitution ): sResolutionTerm = {
    r match {
      case rps: ResolutionProofSchema => {
        ResolutionProofSchema( rps.name, rps.args.map( x =>
          if ( x.isInstanceOf[IntegerTerm] )
            subst( x.asInstanceOf[IntegerTerm] )
          else if ( x.isInstanceOf[nonVarSclause] ) {
            nonVarSclause( x.asInstanceOf[nonVarSclause].ant.map( f => subst( f ).asInstanceOf[SchemaFormula] ), x.asInstanceOf[nonVarSclause].succ.map( f => subst( f ).asInstanceOf[SchemaFormula] ) )
          } else if ( x.isInstanceOf[sClauseComposition] ) {
            sClauseComposition( apply( x.asInstanceOf[sClauseComposition].sclause1, subst ).asInstanceOf[sClause], apply( x.asInstanceOf[sClauseComposition].sclause2, subst ).asInstanceOf[sClause] )
          } else x ) )
      }
      case t: rTerm              => rTerm( apply( t.left, subst ), apply( t.right, subst ), subst( t.atom ).asInstanceOf[SchemaFormula] )
      case non: nonVarSclause    => nonVarSclause( non.ant.map( f => subst( f ).asInstanceOf[SchemaFormula] ), non.succ.map( f => subst( f ).asInstanceOf[SchemaFormula] ) )
      case c: sClauseComposition => sClauseComposition( apply( c.sclause1, subst ).asInstanceOf[sClause], apply( c.sclause2, subst ).asInstanceOf[sClause] )
      case _                     => r
    }
  }
}

//substitution for the  sClauseVar X in a resolution term
object sClauseVarSubstitution {
  def apply( rho: sResolutionTerm, mapX: Map[sClauseVar, sClause] ): sResolutionTerm = {
    rho match {
      case x: sClauseVar if mapX.contains( x ) => mapX.get( x ).get
      case r: rTerm => {
        rTerm( apply( r.left, mapX ), apply( r.right, mapX ), r.atom )
      }
      case comp: sClauseComposition => deComposeSClause( sClauseComposition( apply( comp.sclause1, mapX ).asInstanceOf[sClause], apply( comp.sclause2, mapX ).asInstanceOf[sClause] ) )
      //case c:clauseSchema => TODO
      case rps: ResolutionProofSchema => ResolutionProofSchema( rps.name, rps.args.map( x =>
        if ( x.isInstanceOf[sResolutionTerm] ) {
          sClauseVarSubstitution( x.asInstanceOf[sResolutionTerm], mapX )
        } else x ) )
      case _ => {
        rho
      }
    }
  }
}

//substitution for all variables of type ω and unfolding the sTerms
//it has to be applied after  sClauseVarSubstitution !!!
object unfoldingAtomsInResTerm {
  def apply( rho: sResolutionTerm, trs: dbTRSsTermN, subst: SchemaSubstitution ): sResolutionTerm = {
    rho match {
      case x: sClauseVar => throw new Exception( "Res.term " + rho + "contains X vars !" )
      case non: nonVarSclause => {
        val ground = nonVarSclause( non.ant.map( f => subst( f ).asInstanceOf[SchemaFormula] ), non.succ.map( f => subst( f ).asInstanceOf[SchemaFormula] ) )
        nonVarSclause( ground.ant.map( f => unfoldGroundAtom( f, trs ) ), ground.succ.map( f => unfoldGroundAtom( f, trs ) ) )
      }
      case r: rTerm => {
        rTerm( apply( r.left, trs, subst ), apply( r.right, trs, subst ), unfoldGroundAtom( subst( r.atom ).asInstanceOf[SchemaFormula], trs ) )
      }
      case comp: sClauseComposition => sClauseComposition( apply( comp.sclause1, trs, subst ).asInstanceOf[sClause], apply( comp.sclause2, trs, subst ).asInstanceOf[sClause] )
      //        case c:clauseSchema => TODO
      case _                        => rho
    }
  }
}

// FIXME: if this is actually supposed to be a substitution, then it must be
// possible to use the one implemented on the schema or hol layers. If this is
// supposed to do something different than regular substitution, please use
// another name and/or put a comment here!
object fo2SubstDB extends Iterable[( fo2Var, SchemaExpression )] {
  val map = new scala.collection.mutable.HashMap[fo2Var, SchemaExpression]
  def get( name: fo2Var ) = map( name )
  def clear = map.clear
  def add( v: fo2Var, term: SchemaExpression ): Unit = {
    map.put( v, term )
  }
  def iterator = map.iterator
}

// a substitution for the second-order variables of type : ω->ι
// it is applied after unfoldingAtomsInResTerm, i.e. after the substitution of all ω and X variables
object fo2VarSubstitution {
  def apply( r: sResolutionTerm, mapfo2: Map[fo2Var, SchemaExpression] ): sResolutionTerm = r match {
    case r: rTerm =>
      rTerm( apply( r.left, mapfo2 ).asInstanceOf[sResolutionTerm], apply( r.right, mapfo2 ).asInstanceOf[sResolutionTerm], apply( r.atom, mapfo2 ).asInstanceOf[SchemaFormula] )
    case _ => r
  }

  def apply( c: sClause, mapfo2: Map[fo2Var, SchemaExpression] ): sClause = c match {
    case non: nonVarSclause => nonVarSclause( non.ant.map( f => apply( f, mapfo2 ).asInstanceOf[SchemaFormula] ), non.succ.map( f => apply( f, mapfo2 ).asInstanceOf[SchemaFormula] ) )
    case _                  => c
  }

  def apply( o: SchemaExpression, mapfo2: Map[fo2Var, SchemaExpression] ): SchemaExpression = o match {
    //  case r:rTerm => 
    //    rTerm(apply(r.left, mapfo2).asInstanceOf[sResolutionTerm], apply(r.right, mapfo2).asInstanceOf[sResolutionTerm], apply(r.atom, mapfo2).asInstanceOf[SchemaFormula])

    case SchemaAtom( name, args ) =>
      val newAtomName = Const( name.toString, args.reverse.map( x => x.exptype ).foldRight( To.asInstanceOf[Ty] )( ( x, t ) => x -> t ) )
      unfoldGroundAtom( SchemaAtom( newAtomName, args.map( x =>
        apply( apply( x, mapfo2 ), mapfo2 ) ) ) )

    case Imp( f1, f2 ) => Imp( apply( f1, mapfo2 ).asInstanceOf[SchemaFormula], apply( f2, mapfo2 ).asInstanceOf[SchemaFormula] )
    case And( f1, f2 ) => And( apply( f1, mapfo2 ).asInstanceOf[SchemaFormula], apply( f2, mapfo2 ).asInstanceOf[SchemaFormula] )
    case Or( f1, f2 )  => Or( apply( f1, mapfo2 ).asInstanceOf[SchemaFormula], apply( f2, mapfo2 ).asInstanceOf[SchemaFormula] )
    case App( v, index ) if index.exptype == Tindex => {
      println( "v = " + v.toString )
      println( "index = " + index.toString )
      val exp = App( mapfo2.get( v.asInstanceOf[fo2Var] ).get, index )
      val beta = betaReduce( exp )
      unfoldSTerm( beta )
    }
    case foTerm( v, arg ) if v.exptype == Ti -> Ti => foTerm( v, apply( arg, mapfo2 ) :: Nil )

    case sTerm( v, i, args )                       => unfoldSTerm( o )

    //case non: nonVarSclause => nonVarSclause(non.ant.map(f => apply(f, mapfo2).asInstanceOf[SchemaFormula]), non.succ.map(f => apply(f, mapfo2).asInstanceOf[SchemaFormula]))
    case indexedFOVar( name, index ) =>
      val z = fo2Var( name )
      apply( App( z, index ), mapfo2 )

    case _ => o
  }
}

object ResDeductionToLKTree {
  val nLine = sys.props( "line.separator" )

  def apply( r: sResolutionTerm ): LKProof = r match {
    case non: nonVarSclause =>
      Axiom( non.ant, non.succ )
    case t: rTerm => {
      val up1 = apply( t.left )
      val up2 = apply( t.right )
      if ( !up1.root.succedent.map( fo => fo.formula ).filter( x => x.syntaxEquals( t.atom ) ).isEmpty && !up2.root.antecedent.map( fo => fo.formula ).filter( x => x.syntaxEquals( t.atom ) ).isEmpty ) {
        val left = up1.root.succedent.filter( fo => fo.formula.syntaxEquals( t.atom ) ).tail.foldLeft( up1 )( ( acc, fo ) => ContractionRightRule( acc, fo.formula ) )
        val right = up2.root.antecedent.filter( fo => fo.formula.syntaxEquals( t.atom ) ).tail.foldLeft( up2 )( ( acc, fo ) => ContractionLeftRule( acc, fo.formula ) )
        if ( !left.root.succedent.map( fo => fo.formula ).filter( x => x.syntaxEquals( t.atom ) ).isEmpty ) {
          return CutRule( left, right, t.atom )
        } else {
          return CutRule( right, left, t.atom )
        }
      }
      val right = if ( up1.root.antecedent.filter( fo => fo.formula.syntaxEquals( t.atom ) ).isEmpty )
        up1
      else
        up1.root.antecedent.filter( fo => fo.formula.syntaxEquals( t.atom ) ).tail.foldLeft( up1 )( ( acc, fo ) => ContractionLeftRule( acc, fo.formula ) )
      val left = if ( up2.root.succedent.filter( fo => fo.formula.syntaxEquals( t.atom ) ).isEmpty )
        up2
      else
        up2.root.succedent.filter( fo => fo.formula.syntaxEquals( t.atom ) ).tail.foldLeft( up2 )( ( acc, fo ) => ContractionRightRule( acc, fo.formula ) )
      if ( !left.root.succedent.map( fo => fo.formula ).filter( x => x.syntaxEquals( t.atom ) ).isEmpty ) {
        return CutRule( left, right, t.atom )
      } else {
        CutRule( right, left, t.atom )
      }
    }
    case _ => throw new Exception( nLine + "Error in ResDeductionToLKTree !" + nLine )
  }
}

//--------------------------------------------------

//unfolds a ground resolution proof schema
object unfoldResolutionProofSchema {
  def apply( rho: sResolutionTerm ): sResolutionTerm = {
    val k = IntVar( "k" )
    rho match {
      case rho1: ResolutionProofSchema if resolutionProofSchemaDB.map.contains( rho1.name ) => {
        if ( rho1.args.head == IntZero() ) {
          val base = resolutionProofSchemaDB.map.get( rho1.name ).get._1._2
          base
        } else {
          val step2 = resolutionProofSchemaDB.map.get( rho1.name ).get._2._2
          val map = Map.empty[Var, SchemaExpression] + Tuple2( k, Pred( rho1.args.head.asInstanceOf[IntegerTerm] ) )
          val subst = SchemaSubstitution( map )
          val rho_subst = IntVarSubstitution( step2, subst )
          apply( rho_subst )
        }
      }
      case r: rTerm => {
        var left = apply( r.left )
        var right = apply( r.right )
        if ( left.isInstanceOf[nonVarSclause] )
          left = nonVarSclause( left.asInstanceOf[nonVarSclause].ant.map( f => unfoldGroundAtom( f ) ), left.asInstanceOf[nonVarSclause].succ.map( f => unfoldGroundAtom( f ) ) )
        if ( right.isInstanceOf[nonVarSclause] ) {
          right = nonVarSclause( right.asInstanceOf[nonVarSclause].ant.map( f => unfoldGroundAtom( f ) ), right.asInstanceOf[nonVarSclause].succ.map( f => unfoldGroundAtom( f ) ) )
        }
        rTerm( left, right, unfoldGroundAtom( r.atom ) )
      }
      case _ => rho
    }
  }
}

// It seems that this object is only used for ProofTool,
// so it was renamed to a proper name and removed from tests!
object InstantiateResSchema {
  def getCorrectTermAndSubst( term_name: String, inst: Int ): ( sResolutionTerm, SchemaSubstitution ) = {
    val k = IntVar( "k" )
    if ( inst == 0 ) {
      val map = Map[Var, SchemaExpression]() + Tuple2( k, IntZero() )
      val subst = SchemaSubstitution( map )
      val rho1 = resolutionProofSchemaDB.map.get( term_name ).get._1._1
      ( rho1, subst )
    } else {
      val i = toIntegerTerm( inst - 1 )
      val map = Map[Var, SchemaExpression]() + Tuple2( k, i )
      val subst = SchemaSubstitution( map )
      val rho1 = resolutionProofSchemaDB.map.get( term_name ).get._2._1
      ( rho1, subst )
    }
  }

  def apply( term_name: String, inst: Int ): ( String, LKProof ) = {
    val pair = getCorrectTermAndSubst( term_name, inst )
    val rho1step1 = IntVarSubstitution( pair._1, pair._2 )
    val r = unfoldResolutionProofSchema( rho1step1 )
    val mapfo2 = Map[fo2Var, SchemaExpression]() + fo2SubstDB.map.head
    val fo2sub = fo2VarSubstitution( r, mapfo2 ).asInstanceOf[sResolutionTerm]
    val proof = ResDeductionToLKTree( fo2sub )
    val name = term_name + "↓" + inst + "_lk"
    ( name, proof )
  }
}

//grounds a LKS-proof with respect to the variables of type: ω->ι
object GroundingProjections {
  val nLine = sys.props( "line.separator" )

  def apply( p: LKProof, mapfo2: Map[fo2Var, SchemaExpression] ): LKProof = {
    p match {
      case Axiom( seq ) => Axiom( OccSequent(
        seq.antecedent.map( fo => fo.factory.createFormulaOccurrence( fo2VarSubstitution( fo.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula], Nil ) ),
        seq.succedent.map( fo => fo.factory.createFormulaOccurrence( fo2VarSubstitution( fo.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula], Nil ) )
      ) )
      case WeakeningLeftRule( up, _, p1 )           => WeakeningLeftRule( apply( up, mapfo2 ), fo2VarSubstitution( p1.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula] )
      case WeakeningRightRule( up, _, p1 )          => WeakeningRightRule( apply( up, mapfo2 ), fo2VarSubstitution( p1.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula] )
      case ContractionLeftRule( up, _, a1, a2, _ )  => ContractionLeftRule( apply( up, mapfo2 ), fo2VarSubstitution( a1.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula] )
      case ContractionRightRule( up, _, a1, a2, _ ) => ContractionRightRule( apply( up, mapfo2 ), fo2VarSubstitution( a1.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula] )
      case AndLeft1Rule( up, _, a, p )              => AndLeft1Rule( apply( up, mapfo2 ), fo2VarSubstitution( a.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula], fo2VarSubstitution( p.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula] )
      case AndLeft2Rule( up, _, a, p )              => AndLeft2Rule( apply( up, mapfo2 ), fo2VarSubstitution( a.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula], fo2VarSubstitution( p.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula] )
      case AndRightRule( up1, up2, _, a1, a2, _ )   => AndRightRule( apply( up1, mapfo2 ), apply( up2, mapfo2 ), fo2VarSubstitution( a1.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula], fo2VarSubstitution( a2.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula] )
      case OrLeftRule( up1, up2, _, a1, a2, _ )     => OrLeftRule( apply( up1, mapfo2 ), apply( up2, mapfo2 ), fo2VarSubstitution( a1.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula], fo2VarSubstitution( a2.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula] )
      case OrRight1Rule( up, _, a, p )              => OrRight1Rule( apply( up, mapfo2 ), fo2VarSubstitution( a.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula], fo2VarSubstitution( p.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula] )
      case OrRight2Rule( up, _, a, p )              => OrRight2Rule( apply( up, mapfo2 ), fo2VarSubstitution( a.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula], fo2VarSubstitution( p.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula] )
      case ImpRightRule( up, _, a1, a2, _ )         => ImpRightRule( apply( up, mapfo2 ), fo2VarSubstitution( a1.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula], fo2VarSubstitution( a2.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula] )
      case ImpLeftRule( up1, up2, _, a1, a2, _ )    => ImpLeftRule( apply( up1, mapfo2 ), apply( up2, mapfo2 ), fo2VarSubstitution( a1.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula], fo2VarSubstitution( a2.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula] )
      case NegLeftRule( up, _, a, p )               => NegLeftRule( apply( up, mapfo2 ), fo2VarSubstitution( a.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula] )
      case NegRightRule( up, _, a, p )              => NegRightRule( apply( up, mapfo2 ), fo2VarSubstitution( a.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula] )
      case ForallLeftRule( up, _, a, p, t )         => ForallLeftRule( apply( up, mapfo2 ), fo2VarSubstitution( a.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula], fo2VarSubstitution( p.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula], unfoldSTerm( fo2VarSubstitution( t.asInstanceOf[SchemaExpression], mapfo2 ).asInstanceOf[SchemaExpression] ) )
      case ExistsRightRule( up, _, a, p, t )        => ExistsRightRule( apply( up, mapfo2 ), fo2VarSubstitution( a.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula], fo2VarSubstitution( p.formula.asInstanceOf[SchemaFormula], mapfo2 ).asInstanceOf[SchemaFormula], unfoldSTerm( fo2VarSubstitution( t.asInstanceOf[SchemaExpression], mapfo2 ).asInstanceOf[SchemaExpression] ) )
      case _                                        => throw new Exception( nLine + "Missing case in GroundingProjections !" + nLine + p.rule )
    }
  }
}

