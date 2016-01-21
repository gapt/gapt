package at.logic.gapt.formats.shlk_parsing

import at.logic.gapt.formats.simple.TypeParsers
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lkOld.solve

import scala.util.parsing.combinator._
import scala.util.matching.Regex
import java.io.InputStreamReader
import at.logic.gapt.expr.schema._
import at.logic.gapt.proofs.lkOld.base._
import collection.mutable.{ Map => MMap }
import at.logic.gapt.proofs.shlk._
import scala.Tuple4
import at.logic.gapt.expr.schema.IntZero
import scala.Tuple2
import at.logic.gapt.expr.StringSymbol
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import scala.Tuple4
import at.logic.gapt.expr.schema.IntZero
import scala.Tuple2

object sFOParserCNT {
  val nLine = sys.props( "line.separator" )

  def parseProofs( input: InputStreamReader ): List[( String, LKProof )] = {
    //    ("p",parseProof(input, "root"))::Nil
    val m = sFOParserCNT.parseProof( input )
    m.foldLeft( List.empty[( String, LKProof )] )( ( res, pair ) => ( pair._1, pair._2._1.get( "root" ).get ) :: ( pair._1, pair._2._2.get( "root" ).get ) :: res )
  }

  //--------------------------------- parse SLK proof -----------------------

  def parseProofFlat( txt: InputStreamReader ): MMap[String, Tuple2[LKProof, LKProof]] =
    {
      val map = parseProof( txt )
      map.map( pp => {
        val name = pp._1
        val pair = pp._2
        ( name, Tuple2( pair._1.get( "root" ).get, pair._2.get( "root" ).get ) )
      } )
    }

  //plabel should return the proof corresponding to this label
  def parseProof( txt: InputStreamReader ): MMap[String, Tuple2[MMap[String, LKProof], MMap[String, LKProof]]] = {
    var mapBase = MMap.empty[String, LKProof]
    var mapStep = MMap.empty[String, LKProof]
    var map = MMap.empty[String, LKProof]
    var baseORstep: Int = 1
    SchemaProofDB.clear
    var defMMap = MMap.empty[Const, Tuple2[List[IntegerTerm], SchemaFormula]]
    var list = List[String]()
    var error_buffer = ""
    //    lazy val sp2 = new ParserTxt
    //    sp2.parseAll(sp2.line, txt)
    val bigMMap = MMap.empty[String, Tuple2[MMap[String, LKProof], MMap[String, LKProof]]]
    val mapPredicateToArity = MMap.empty[String, Int]
    dbTRS.clear
    lazy val sp = new SimpleSLKParser

    sp.parseAll( sp.slkProofs, txt ) match {
      case sp.Success( result, input ) => // println( nLine + nLine + "SUCCESS parse :) " + nLine )
      case x: AnyRef => // { println( nLine + nLine + "FAIL parse : " + nLine + error_buffer); throw new Exception( nLine + nLine + "FAIL parse :( " + nLine ); }
        throw new Exception( x.toString )
    }

    class SimpleSLKParser extends JavaTokenParsers with TypeParsers {
      def line: Parser[List[Unit]] = rep( cmappingBase )
      def cmappingBase: Parser[Unit] = ( "comment" ~ "\"[\"]*\"" ) ^^ { x => () } | mappingBase
      def mappingBase: Parser[Unit] = label.r ~ ":" ~ proof ^^ {
        case l ~ ":" ~ p => {
          error_buffer = l
          if ( baseORstep == 2 ) {
            map = MMap.empty[String, LKProof]
            baseORstep = 1
          }
          map.put( l, p )
          mapBase = map
        }
      }

      def mappingStep: Parser[Unit] = label.r ~ ":" ~ proof ^^ {
        case l ~ ":" ~ p => {
          error_buffer = l
          //          mapStep.put(l,p)
          if ( baseORstep == 1 ) {
            map = MMap.empty[String, LKProof]
            baseORstep = 2
          }
          map.put( l, p )
          mapStep = map
        }
      }

      def name = """[\\]*[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,_,0,1,2,3,4,5,6,7,8,9]*""".r
      //~ "(" ~ repsep(term,",") ~ ")"
      def slkProof: Parser[Any] = "proof" ~ name ~ "proves" ~ sequent ~ "base" ~ "{" ~ line ~ "}" ~ "step" ~ "{" ~ rep( mappingStep ) ~ "}" ~ rep( """-""".r ) ^^ {
        case "proof" ~ str ~ str1 ~ seq ~ "base" ~ "{" ~ line1 ~ "}" ~ "step" ~ "{" ~ line2 ~ "}" ~ procents => {
          //          proofName = str
          bigMMap.put( str, Tuple2( mapBase, mapStep ) )
          SchemaProofDB.put( new SchemaProof( str, IntVar( "k" ) :: Nil, seq.toHOLSequent, mapBase.get( "root" ).get, mapStep.get( "root" ).get ) )
          mapBase = MMap.empty[String, LKProof]
          mapStep = MMap.empty[String, LKProof]
          //          println( nLine + nLine + "Parsing is SUCCESSFUL : "+str)
        }
      }

      def slkProofs: Parser[List[Unit]] = rep( trs ) ~ rep( define ) ~ rep( slkProof ) ^^ {
        case a ~ s => {
          List.empty[Unit]
        }
      }

      def trs: Parser[Unit] = s_term ~ "->" ~ term ~ s_term ~ "->" ~ term ^^ {
        case t1 ~ "->" ~ base ~ t2 ~ "->" ~ step => {
          t1 match {
            case sTerm( func1, i1, arg1 ) =>
              t2 match {
                case sTerm( func2, i2, arg2 ) => {
                  //                  if(func1 == func2) {
                  dbTRS.add( func1.asInstanceOf[Const], Tuple2( t1, base ), Tuple2( t2, step ) )
                  //                  }
                }
              }
          }
        }
      }

      def proof: Parser[LKProof] = ax | orL | orR1 | orR | orR2 | negL | negR | cut | pFOLink | andL | andR | andL1 | andL2 | weakL | weakR | contrL | contrR | andEqR1 | andEqR2 | andEqR3 | orEqR1 | orEqR2 | orEqR3 | andEqL1 | andEqL2 | andEqL3 | orEqL1 | orEqL2 | orEqL3 | allL | exR | exL | exLHyper | allR | allRHyper | allLHyper | exRHyper | impL | impR | termDefL1 | termDefR1 | arrowL | foldL | arrowR | autoprop
      def label: String = """[0-9]*[root]*"""

      def formula: Parser[SchemaFormula] = ( atom | neg | big | and | or | indPred | imp | forall | exists | variable | constant | forall_hyper | exists_hyper ) ^? { case trm: SchemaFormula => trm }
      def intTerm: Parser[SchemaExpression] = index //| schemaFormula
      def index: Parser[IntegerTerm] = ( sum | intConst | intVar | succ )
      def intConst: Parser[IntegerTerm] = ( intZero | intOne | intTwo | intThree )
      def intOne: Parser[IntegerTerm] = "1".r ^^ { case x => { Succ( IntZero() ) } }
      def intTwo: Parser[IntegerTerm] = "2".r ^^ { case x => { Succ( Succ( IntZero() ) ) } }
      def intThree: Parser[IntegerTerm] = "3".r ^^ { case x => { Succ( Succ( Succ( IntZero() ) ) ) } }
      def intZero: Parser[IntegerTerm] = "0".r ^^ {
        case x => { IntZero() }
      }
      def PLUSterm: Parser[SchemaExpression] = "(" ~ term ~ "+" ~ term ~ ")" ^^ {
        case "(" ~ t1 ~ "+" ~ t2 ~ ")" => {
          val func = Const( "+", Tindex -> ( Tindex -> Tindex ) )
          App( App( func, t1 ), t2 )
        }
      }
      def MINUSterm: Parser[SchemaExpression] = "(" ~ term ~ "-" ~ term ~ ")" ^^ {
        case "(" ~ t1 ~ "-" ~ t2 ~ ")" => {
          val func = Const( "-", Tindex -> ( Tindex -> Tindex ) )
          App( App( func, t1 ), t2 )
        }
      }

      def MULTterm: Parser[SchemaExpression] = "(" ~ term ~ "*" ~ term ~ ")" ^^ {
        case "(" ~ t1 ~ "*" ~ t2 ~ ")" => {
          val func = Const( "*", Tindex -> ( Tindex -> Tindex ) )
          App( App( func, t1 ), t2 )
        }
      }

      def POWterm: Parser[SchemaExpression] = "EXP(" ~ index ~ "," ~ term ~ ")" ^^ {
        case "EXP(" ~ t1 ~ "," ~ t2 ~ ")" => {
          val func = Const( "EXP", Tindex -> ( Tindex -> Tindex ) )
          App( App( func, t1 ), t2 )
        }
      }
      def sum: Parser[IntegerTerm] = intVar ~ "+" ~ intConst ^^ {
        case indV ~ "+" ~ indC => {
          //        println( nLine + nLine + "sum")
          indC match {
            case Succ( IntZero() )                 => Succ( indV )
            case Succ( Succ( IntZero() ) )         => Succ( Succ( indV ) )
            case Succ( Succ( Succ( IntZero() ) ) ) => Succ( Succ( Succ( indV ) ) )
          }
        }
      }

      def intVar: Parser[IntVar] = "[i,j,k,p,u,q]".r ^^ {
        case x => { /*println( nLine + nLine + "intVar");*/ IntVar( x ) }
      }
      def succ: Parser[IntegerTerm] = "s(" ~ intTerm ~ ")" ^^ {
        case "s(" ~ intTerm ~ ")" => Succ( intTerm.asInstanceOf[IntegerTerm] )
      }

      def schemaFormula = formula

      def indPred: Parser[SchemaFormula] = """[A-Z]*[a-z]*[0-9]*""".r ~ "(" ~ repsep( index, "," ) ~ ")" ^^ {
        case x ~ "(" ~ l ~ ")" => {
          if ( !mapPredicateToArity.isDefinedAt( x.toString ) )
            mapPredicateToArity.put( x.toString, l.size )
          else if ( mapPredicateToArity.get( x.toString ).get != l.size ) {
            println( nLine + "Input ERROR : Indexed Predicate '" + x.toString + "' should have arity " + mapPredicateToArity.get( x.toString ).get + ", but not " + l.size + " !" + nLine + nLine )
            throw new Exception( nLine + "Input ERROR : Indexed Predicate '" + x.toString + "' should have arity " + mapPredicateToArity.get( x.toString ).get + ", but not " + l.size + " !" + nLine )
          }
          //          println( nLine + nLine + "IndexedPredicate");

          //          val map: MMap[Var, T])
          //          val subst: SchemaSubstitution1[SchemaExpression] = new SchemaSubstitution1[SchemaExpression]()
          //          val new_ind = subst(ind)
          //          val new_map = (subst.map - subst.map.head._1.asInstanceOf[Var]) + Tuple2(subst.map.head._1.asInstanceOf[Var], Pred(new_ind.asInstanceOf[IntegerTerm]) )
          //          val new_subst = new SchemaSubstitution1(new_map)

          IndexedPredicate( x, l )
        }
      }

      def define: Parser[Any] = indPred ~ ":=" ~ schemaFormula ^^ {
        case indpred ~ ":=" ~ sf => {
          indpred match {
            case IndexedPredicate( f, ls ) => {
              defMMap.put( f, Tuple2( ls.asInstanceOf[List[IntegerTerm]], sf.asInstanceOf[SchemaFormula] ) )
            }
          }
        }
      }

      // nested bigAnd bigOr....           ("""BigAnd""".r | """BigOr""".r)
      def prefix: Parser[Tuple4[Boolean, IntVar, IntegerTerm, IntegerTerm]] = """[BigAnd]*[BigOr]*""".r ~ "(" ~ intVar ~ "=" ~ index ~ ".." ~ index ~ ")" ^^ {
        case "BigAnd" ~ "(" ~ intVar1 ~ "=" ~ ind1 ~ ".." ~ ind2 ~ ")" => {
          //          println( nLine + nLine + "prefix" + nLine + nLine )
          Tuple4( true, intVar1, ind1, ind2 )
        }
        case "BigOr" ~ "(" ~ intVar1 ~ "=" ~ ind1 ~ ".." ~ ind2 ~ ")" => {
          //          println( nLine + nLine + "prefix" + nLine + nLine )
          Tuple4( false, intVar1, ind1, ind2 )
        }
      }

      def big: Parser[SchemaFormula] = rep1( prefix ) ~ schemaFormula ^^ {
        case l ~ schemaFormula => {
          //          println("Works?")
          l.reverse.foldLeft( schemaFormula.asInstanceOf[SchemaFormula] )( ( res, triple ) => {
            if ( triple._1 )
              BigAnd( triple._2, res, triple._3, triple._4 )
            else
              BigOr( triple._2, res, triple._3, triple._4 )
          } )
        }
      }
      def term: Parser[SchemaExpression] = ( lambdaTerm | PLUSterm | MINUSterm | MULTterm | POWterm | index | fo_term | s_term | abs | variable | constant | var_func | const_func | SOindVar )
      def lambdaTerm: Parser[SchemaExpression] = "(" ~ "λ" ~ FOVariable ~ "." ~ intZero ~ ")" ^^ {
        case "(" ~ "λ" ~ x ~ "." ~ zero ~ ")" => Abs( x, zero )
      }
      def s_term: Parser[SchemaExpression] = "[g,h]".r ~ "(" ~ intTerm ~ "," ~ term ~ ")" ^^ {
        case name ~ "(" ~ i ~ "," ~ args ~ ")" => {
          //          println( nLine + "sTerm : "+name+"("+i+","+args+")")
          //          println("args = "+args)
          //                    println("args.extype = "+args.exptype)
          sTerm( name, i, args :: Nil )
        }
      }
      def fo_term: Parser[SchemaExpression] = "[f]".r ~ "(" ~ term ~ ")" ^^ {
        case name ~ "(" ~ arg ~ ")" => {
          //     println( nLine + nLine + "foTerm" + nLine + " arg.extype = "+arg.exptype)
          foTerm( name, arg :: Nil )
        }
      }
      def indexedVar: Parser[Var] = regex( new Regex( "[zzz]" ) ) ~ "(" ~ intTerm ~ ")" ^^ {
        case x ~ "(" ~ index ~ ")" => {
          indexedFOVar( x, index.asInstanceOf[IntegerTerm] )
        }
      }
      //indexed variable of type ω->ω
      def indexedwVar: Parser[Var] = regex( new Regex( "[α,c,b,y,a,x,z,s,w,h,m,n,l]" ) ) ~ "(" ~ intTerm ~ ")" ^^ {
        case x ~ "(" ~ index ~ ")" => {
          indexedOmegaVar( x, index.asInstanceOf[IntegerTerm] )
        }
      }

      // TODO: a should be a FOConstant
      def FOVariable: Parser[Var] = regex( new Regex( "[x,v,g,u,q]" + word ) ) ^^ { case x => fowVar( x ) } //foVar(x)}
      def variable: Parser[Var] = ( indexedwVar | indexedVar | FOVariable ) //regex(new Regex("[u-z]" + word))  ^^ {case x => Var(new VariableStringSymbol(x), i->i).asInstanceOf[Var]}
      def constant: Parser[Const] = regex( new Regex( "[t]" + word ) ) ^^ {
        case x => {
          Const( StringSymbol( x ), Tindex -> Tindex )
        }
      }
      def and: Parser[SchemaFormula] = "(" ~ repsep( formula, "/\\" ) ~ ")" ^^ { case "(" ~ formulas ~ ")" => { formulas.tail.foldLeft( formulas.head )( ( f, res ) => And( f, res ) ) } }
      def or: Parser[SchemaFormula] = "(" ~ repsep( formula, """\/""" ) ~ ")" ^^ { case "(" ~ formulas ~ ")" => { formulas.tail.foldLeft( formulas.head )( ( f, res ) => Or( f, res ) ) } }
      def imp: Parser[SchemaFormula] = "(" ~ formula ~ "->" ~ formula ~ ")" ^^ { case "(" ~ x ~ "->" ~ y ~ ")" => Imp( x, y ) }
      def abs: Parser[SchemaExpression] = "Abs" ~ variable ~ term ^^ { case "Abs" ~ v ~ x => Abs( v, x ).asInstanceOf[SchemaExpression] }
      def neg: Parser[SchemaFormula] = "~" ~ formula ^^ { case "~" ~ x => Neg( x ) }
      def atom: Parser[SchemaFormula] = ( inequality | equality | less | lessOrEqual | s_atom | var_atom | const_atom )
      def forall: Parser[SchemaFormula] = "Forall" ~ variable ~ formula ^^ { case "Forall" ~ v ~ x => All( v, x ) }
      def forall_hyper: Parser[SchemaFormula] = "ForallHyper" ~ SOindVar ~ formula ^^ { case "ForallHyper" ~ v ~ x => All( v, x ) }
      def exists: Parser[SchemaFormula] = "Exists" ~ variable ~ formula ^^ { case "Exists" ~ v ~ x => Ex( v, x ) }
      def exists_hyper: Parser[SchemaFormula] = "ExistsHyper" ~ SOindVar ~ formula ^^ { case "ExistsHyper" ~ v ~ x => Ex( v, x ) }

      def var_atom: Parser[SchemaFormula] = regex( new Regex( "[u-z]" + word ) ) ~ "(" ~ repsep( term, "," ) ~ ")" ^^ {
        case x ~ "(" ~ params ~ ")" =>
          SchemaAtom( Var( x, FunctionType( To, params map ( _.exptype ) ) ), params )
      }
      //      def const_atom: Parser[SchemaFormula] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
      def const_atom: Parser[SchemaFormula] = regex( new Regex( "[P]" ) ) ~ "(" ~ repsep( term, "," ) ~ ")" ^^ {
        case x ~ "(" ~ params ~ ")" =>
          SchemaAtom( Const( x, FunctionType( To, params map ( _.exptype ) ) ), params )
      }
      def s_atom: Parser[SchemaFormula] = """[BEΣCO]*""".r ~ "(" ~ repsep( term, "," ) ~ ")" ^^ {
        case x ~ "(" ~ params ~ ")" =>
          //TODO: refactor rule to parse only the correct terms
          require( params.size > 0, "A schematic atom needs at least one parameter (of type omega)!" ) //TODO: requirement added later, might break some test cases
          require( params( 0 ).exptype == Tindex, "The first parameter of a schematic formula needs to be of type omega!" ) //TODO: requirement added later, might break some test cases
          SchemaAtom( Const( x, FunctionType( To, params map ( _.exptype ) ) ), params )
      }
      def equality: Parser[SchemaFormula] = eq_infix | eq_prefix // infix is problematic in higher order
      def eq_infix: Parser[SchemaFormula] = term ~ "=" ~ term ^^ { case x ~ "=" ~ y => Eq( x, y ) }
      def inequality: Parser[SchemaFormula] = term ~ "\\=" ~ term ^^ { case x ~ "\\=" ~ y => Neg( Eq( x, y ) ) }
      def eq_prefix: Parser[SchemaFormula] = "=" ~ "(" ~ term ~ "," ~ term ~ ")" ^^ { case "=" ~ "(" ~ x ~ "," ~ y ~ ")" => Eq( x, y ) }
      def less: Parser[SchemaFormula] = term ~ "<" ~ term ^^ { case x ~ "<" ~ y => lessThan( x, y ) }
      def lessOrEqual: Parser[SchemaFormula] = term ~ "<=" ~ term ^^ { case x ~ "<=" ~ y => leq( x, y ) }
      def var_func: Parser[SchemaExpression] = regex( new Regex( "[u-z]" + word ) ) ~ "(" ~ repsep( term, "," ) ~ ")" ^^ {
        case x ~ "(" ~ params ~ ")" =>
          SchemaFunction( Var( x, FunctionType( Tindex -> Tindex, params map ( _.exptype ) ) ), params )
      }
      def SOindVar: Parser[Var] = regex( new Regex( "[x,c,w,h,a,z,b,b',l,f,r,m,y,A,B]" ) ) ^^ { case x => Var( x, Tindex -> Tindex ) }
      /*def var_func: Parser[SchemaExpression] = (var_func1 | var_funcn)
      def var_func1: Parser[SchemaExpression] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ~ ":" ~ Type ^^ {case x ~ "(" ~ params ~ ")" ~ ":" ~ tp => Function(new VariableStringSymbol(x), params, tp)}
      def var_funcn: Parser[SchemaExpression] = regex(new Regex("[u-z]" + word)) ~ "^" ~ decimalNumber ~ "(" ~ repsep(term,",") ~ ")"  ~ ":" ~ Type ^^ {case x ~ "^" ~ n ~ "(" ~ params ~ ")" ~ ":" ~ tp => genF(n.toInt, Var(new VariableStringSymbol(x)), params)}
      */
      def const_func: Parser[SchemaExpression] = "[v]" ~ "(" ~ repsep( term, "," ) ~ ")" ^^ {
        case x ~ "(" ~ params ~ ")" =>
          SchemaFunction( Const( x, FunctionType( Tindex -> Tindex, params map ( _.exptype ) ) ), params )
      }
      protected def word: String = """[a-zA-Z0-9$_{}]*"""
      protected def symbol: Parser[String] = symbols.r
      def symbols: String = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073\0173\0175]+""" // +-*/\^<>=`~?@&|!#{}';

      //      def sequent: Parser[Sequent] = formula ~ "|-" ~ formula ^^ { case lf ~ "|-" ~ rf => {
      def sequent: Parser[OccSequent] = repsep( formula, "," ) ~ "|-" ~ repsep( formula, "," ) ^^ {
        case lfs ~ "|-" ~ rfs => {
          //          println( nLine + nLine + "SEQUENT")
          Axiom( lfs, rfs ).root
        }
      }

      def ax: Parser[LKProof] = "ax(" ~ sequent ~ ")" ^^ {
        case "ax(" ~ sequent ~ ")" => {
          //          println( nLine + nLine + "AXIOM")
          Axiom( sequent )
        }
        case _ => { println( "ERROR" ); Axiom( List(), List() ) }
      }

      def proof_name: Parser[String] = """[\\]*[a-z]*[0-9]*""".r

      //      def pLink: Parser[LKProof] = "pLink(" ~ "(" ~ proof_name ~ "," ~ index ~ ")"  ~ sequent ~ ")" ^^ {
      //        case                       "pLink(" ~ "(" ~ name ~       "," ~   v   ~ ")"  ~ sequent ~ ")" => {
      ////          println( nLine + nLine + "pLink")
      //          SchemaProofLinkRule(sequent.toHOLSequent, name, v::Nil)
      //        }
      //      }

      def pFOLink: Parser[LKProof] = "pLink(" ~ "(" ~ proof_name ~ "," ~ repsep( term, "," ) ~ ")" ~ sequent ~ ")" ^^ {
        case "pLink(" ~ "(" ~ name ~ "," ~ l ~ ")" ~ sequent ~ ")" => {
          //          println( nLine + nLine + "pLink")
          FOSchemaProofLinkRule( sequent.toHOLSequent, name, l )
        }
      }

      def orR1: Parser[LKProof] = "orR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          //          println( nLine + nLine + "orR1")
          OrRight1Rule( map.get( l ).get, f1, f2 )
        }
      }

      def orR2: Parser[LKProof] = "orR2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orR2(" ~ label ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          //          println( nLine + nLine + "orR2")
          OrRight2Rule( map.get( label ).get, f1, f2 )
        }
      }

      def orR: Parser[LKProof] = "orR(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orR(" ~ label ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          //          println( nLine + nLine + "orR")
          OrRightRule( map.get( label ).get, f1, f2 )
        }
      }

      def orL: Parser[LKProof] = "orL(" ~ label.r ~ "," ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orL(" ~ l1 ~ "," ~ l2 ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          //          println( nLine + nLine + "orL")
          OrLeftRule( map.get( l1 ).get, map.get( l2 ).get, f1, f2 )
        }
      }

      def andR: Parser[LKProof] = "andR(" ~ label.r ~ "," ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andR(" ~ l1 ~ "," ~ l2 ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          //          println( nLine + nLine + "andR")
          //          println( nLine + "error_buffer = "+error_buffer)
          //          println( nLine + map.get(l).get.root.toString)
          //          println(map.get(l1).get.root)
          //          println( nLine + nLine )
          //          println(map.get(l2).get.root)
          //          println( nLine + nLine )
          val p = AndRightRule( map.get( l1 ).get, map.get( l2 ).get, f1, f2 )
          //          println(p.root)
          p
        }
      }

      def cut: Parser[LKProof] = "cut(" ~ label.r ~ "," ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "cut(" ~ l1 ~ "," ~ l2 ~ "," ~ f ~ ")" => {
          //          println( nLine + nLine + "cut")
          //          println( nLine + "error_buffer = "+error_buffer)

          CutRule( map.get( l1 ).get, map.get( l2 ).get, f )
        }
      }

      def negL: Parser[LKProof] = "negL(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "negL(" ~ label ~ "," ~ formula ~ ")" => {
          //          println( nLine + nLine + "negL")
          NegLeftRule( map.get( label ).get, formula )
        }
        case _ => {
          println( nLine + nLine + "Error!" )
          sys.exit( 10 )
        }
      }

      def negR: Parser[LKProof] = "negR(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "negR(" ~ label ~ "," ~ formula ~ ")" => {
          //          println( nLine + nLine + map.get(label).get.root.toString)
          //          println( nLine + nLine + "negR")
          NegRightRule( map.get( label ).get, formula )
        }
      }

      def weakR: Parser[LKProof] = "weakR(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "weakR(" ~ label ~ "," ~ formula ~ ")" => {
          //          println( nLine + nLine + "weakR")
          WeakeningRightRule( map.get( label ).get, formula )
        }
      }

      def weakL: Parser[LKProof] = "weakL(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "weakL(" ~ label ~ "," ~ formula ~ ")" => {
          //          println( nLine + nLine + "weakL")
          WeakeningLeftRule( map.get( label ).get, formula )
        }
      }
      //      def eqAnd1: Parser[LKProof] = "eqAnd1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
      //        case "eqAnd1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
      //          AndEquivalenceRule1(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
      //        }
      //      }

      def andL1: Parser[LKProof] = "andL1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andL1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          //          println( nLine + nLine + "andL1")
          AndLeft1Rule( map.get( l ).get, f1, f2 )
        }
      }

      def andL2: Parser[LKProof] = "andL2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andL2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          //          println( nLine + nLine + "andL2")
          AndLeft2Rule( map.get( l ).get, f1, f2 )
        }
      }

      def andL: Parser[LKProof] = "andL(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andL(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          //          println( nLine + nLine + "andL")
          //          println( nLine + "error_buffer = "+error_buffer)
          //          println( nLine + map.get(l).get.root.toString)
          val p = AndLeftRule( map.get( l ).get, f1, f2 )
          p
          //          val and = And(f1,f2)
          //          val aux = p.root.antecedent.tail.head.formula
          //          println( nLine + "p   = "+aux)
          //          println( nLine + "and = "+and)
          //          println( nLine + nLine + aux.syntaxEquals(and))
          //          println( nLine + "f1 = "+f1)
          //          var res = p
          //          f1 match {
          //            case BigAnd(ind,f,lb,ub) => {
          //              println("ERROR 5")
          ////              sys.exit(1)
          //              res = AndEquivalenceRule1(p, and.asInstanceOf[SchemaFormula], BigAnd(ind,f,lb,Succ(ub)).asInstanceOf[SchemaFormula])
          //              println( nLine + nLine + "res = "+res.root.antecedent.head.formula)
          ////              return res
          //              res
          //            }
          //            case _ => {
          //              println("ERROR 3")
          ////              sys.exit(1)
          //              res
          //            }
          //          }
          //          println("ERROR 2")
          //          res
          //              sys.exit(1)
        }
      }

      def andEqR1: Parser[LKProof] = "andEqR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndRightEquivalenceRule1( map.get( l ).get, f1, f2 )
        }
      }

      def andEqR2: Parser[LKProof] = "andEqR2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqR2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndRightEquivalenceRule2( map.get( l ).get, f1, f2 )
        }
      }

      def andEqR3: Parser[LKProof] = "andEqR3(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqR3(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndRightEquivalenceRule3( map.get( l ).get, f1, f2 )
        }
      }

      def andEqL1: Parser[LKProof] = "andEqL1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqL1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndLeftEquivalenceRule1( map.get( l ).get, f1, f2 )
        }
      }

      def andEqL2: Parser[LKProof] = "andEqL2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqL2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndLeftEquivalenceRule2( map.get( l ).get, f1, f2 )
        }
      }

      def andEqL3: Parser[LKProof] = "andEqL3(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqL3(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndLeftEquivalenceRule3( map.get( l ).get, f1, f2 )
        }
      }

      def orEqR1: Parser[LKProof] = "orEqR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orEqR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          OrRightEquivalenceRule1( map.get( l ).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula] )
        }
      }

      def orEqR2: Parser[LKProof] = "orEqR2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orEqR2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          OrRightEquivalenceRule2( map.get( l ).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula] )
        }
      }

      def orEqR3: Parser[LKProof] = "orEqR3(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orEqR3(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          OrRightEquivalenceRule3( map.get( l ).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula] )
        }
      }

      def orEqL1: Parser[LKProof] = "orEqL1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orEqL1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          OrLeftEquivalenceRule1( map.get( l ).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula] )
        }
      }

      def orEqL2: Parser[LKProof] = "orEqL2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orEqL2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          OrLeftEquivalenceRule2( map.get( l ).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula] )
        }
      }

      def orEqL3: Parser[LKProof] = "orEqL3(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orEqL3(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          OrLeftEquivalenceRule3( map.get( l ).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula] )
        }
      }

      def contrL: Parser[LKProof] = "contrL(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "contrL(" ~ l ~ "," ~ f ~ ")" => {
          //          println( nLine + nLine + "contrL")
          ContractionLeftRule( map.get( l ).get, f )
        }
      }

      def contrR: Parser[LKProof] = "contrR(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "contrR(" ~ l ~ "," ~ f ~ ")" => {
          //          println( nLine + nLine + "contrR")
          ContractionRightRule( map.get( l ).get, f )
        }
      }

      def exR: Parser[LKProof] = "exR(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ term ~ ")" ^^ {
        case "exR(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ term ~ ")" => {
          ExistsRightRule( map.get( l ).get, aux.asInstanceOf[SchemaFormula], main.asInstanceOf[SchemaFormula], term.asInstanceOf[SchemaExpression] )
        }
      }

      def allL: Parser[LKProof] = "allL(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ term ~ ")" ^^ {
        case "allL(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ term ~ ")" => {
          ForallLeftRule( map.get( l ).get, aux.asInstanceOf[SchemaFormula], main.asInstanceOf[SchemaFormula], term.asInstanceOf[SchemaExpression] )
        }
      }

      def allR: Parser[LKProof] = "allR(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ ( indexedwVar | FOVariable ) ~ ")" ^^ {
        case "allR(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ v ~ ")" => {
          ForallRightRule( map.get( l ).get, aux.asInstanceOf[SchemaFormula], main.asInstanceOf[SchemaFormula], v.asInstanceOf[Var] )
        }
      }

      def exL: Parser[LKProof] = "exL(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ ( indexedwVar | FOVariable ) ~ ")" ^^ {
        case "exL(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ v ~ ")" => {
          ExistsLeftRule( map.get( l ).get, aux.asInstanceOf[SchemaFormula], main.asInstanceOf[SchemaFormula], v.asInstanceOf[Var] )
        }
      }

      def exLHyper: Parser[LKProof] = "exLHyper(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ SOindVar ~ ")" ^^ {
        case "exLHyper(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ v ~ ")" => {
          ExistsHyperLeftRule( map.get( l ).get, aux.asInstanceOf[SchemaFormula], main.asInstanceOf[SchemaFormula], v.asInstanceOf[Var] )
        }
      }

      def allRHyper: Parser[LKProof] = "allRHyper(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ SOindVar ~ ")" ^^ {
        case "allRHyper(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ v ~ ")" => {
          ForallHyperRightRule( map.get( l ).get, aux.asInstanceOf[SchemaFormula], main.asInstanceOf[SchemaFormula], v.asInstanceOf[Var] )
        }
      }

      def exRHyper: Parser[LKProof] = "exRHyper(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ term ~ ")" ^^ {
        case "exRHyper(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ t ~ ")" => {
          ExistsHyperRightRule( map.get( l ).get, aux, main, t )
        }
      }

      def allLHyper: Parser[LKProof] = "allLHyper(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ term ~ ")" ^^ {
        case "allLHyper(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ t ~ ")" => {
          ForallHyperLeftRule( map.get( l ).get, aux, main, t )
        }
      }

      def impL: Parser[LKProof] = "impL(" ~ label.r ~ "," ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "impL(" ~ l1 ~ "," ~ l2 ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          ImpLeftRule( map.get( l1 ).get, map.get( l2 ).get, f1, f2 )
        }
      }

      def impR: Parser[LKProof] = "impR(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "impR(" ~ label ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          ImpRightRule( map.get( label ).get, f1, f2 )
        }
      }

      def foldL: Parser[LKProof] = "foldL(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "foldL(" ~ label ~ "," ~ aux ~ "," ~ main ~ ")" => {
          foldLeftRule( map.get( label ).get, aux, main )
        }
      }

      def arrowL: Parser[LKProof] = "arrowL(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "arrowL(" ~ label ~ "," ~ f1 ~ ")" => {
          trsArrowLeftRule( map.get( label ).get, f1 )
        }
      }

      def arrowR: Parser[LKProof] = "arrowR(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "arrowR(" ~ label ~ "," ~ f1 ~ ")" => {
          trsArrowRightRule( map.get( label ).get, f1 )
        }
      }

      def autoprop: Parser[LKProof] = "autoprop(" ~ sequent ~ ")" ^^ {
        case "autoprop(" ~ seq ~ ")" => solve.solvePropositional( seq.toHOLSequent, throwOnError = true ).get
      }

      def termDefL1: Parser[LKProof] = "termDefL1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "termDefL1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          TermLeftEquivalenceRule1( map.get( l ).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula] )
        }
      }

      def termDefR1: Parser[LKProof] = "termDefR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "termDefR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          TermRightEquivalenceRule1( map.get( l ).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula] )
        }
      }
    }
    //    println( nLine + nLine + "number of SLK-proofs = "+bigMMap.size)
    //    println( nLine + "defMMapr size = "+defMMap.size)

    //    println( nLine + nLine + nLine + "list = "+list)
    //    if (!bigMMap.get("chi").get._2.isDefinedAt(plabel)) println( nLine + nLine + nLine + "Syntax ERROR after ID : " + error_buffer + nLine + nLine)
    //    val m = bigMMap.get("chi").get._2.get(plabel).get
    ////    println(m.root.antecedent.head+" |- "+m.root.succedent.head)
    //    m
    //  println( nLine + "SchemaProofDB.size = "+SchemaProofDB.size + nLine )
    bigMMap
  }
}

object getPLinks {
  val nLine = sys.props( "line.separator" )

  def apply( p: LKProof ): List[OccSequent] = p match {
    case Axiom( so ) => Nil
    case UnaryLKProof( _, upperProof, _, _, _ ) => apply( upperProof )
    case BinaryLKProof( _, upperProofLeft, upperProofRight, _, aux1, aux2, _ ) => apply( upperProofLeft ) ::: apply( upperProofRight )
    case UnarySchemaProof( _, upperProof, _, _, _ ) => apply( upperProof )
    case SchemaProofLinkRule( so, name, indices ) => so :: Nil
    case TermEquivalenceRule1( upperProof, _, _, _ ) => apply( upperProof )
    case ForallHyperLeftRule( upperProof, r, a, p, _ ) => apply( upperProof )
    case ExistsHyperRightRule( upperProof, r, a, p, _ ) => apply( upperProof )
    case ForallHyperRightRule( upperProof, r, a, p, _ ) => apply( upperProof )
    case ExistsHyperLeftRule( upperProof, r, a, p, _ ) => apply( upperProof )
    case _ => throw new Exception( nLine + "Missin rule in getPLinks.apply" + nLine )
  }
}

//makes a clauses CL,A|-C,D  and CL|-E,F to CL|-(~A\/C\/D) /\ (E\/F)
object ClauseSetToCNF {
  //returns: CL |- formulaList
  def apply( seq: HOLSequent ): HOLSequent = {
    val headCLsym = seq.antecedent.head
    if ( seq.antecedent.size == 1 && seq.succedent.size <= 1 )
      return seq
    else if ( seq.antecedent.size == 1 )
      return HOLSequent( headCLsym :: Nil, Or( seq.succedent.toList.asInstanceOf[List[SchemaFormula]] ) :: Nil )
    val succ = Or( seq.antecedent.tail.toList.map( f =>
      Neg( f.asInstanceOf[SchemaFormula] ) ) ++ seq.succedent.asInstanceOf[List[SchemaFormula]] )
    HOLSequent( headCLsym :: Nil, succ :: Nil )
  }

  var mapCLsym: MMap[SchemaFormula, List[SchemaFormula]] = MMap.empty[SchemaFormula, List[SchemaFormula]]

  def combiningCLsymbols( ccs: List[HOLSequent] ): MMap[SchemaFormula, List[SchemaFormula]] = {
    ccs.map( fseq => {
      //      println( nLine + "combining: "+mapCLsym)
      val seq: HOLSequent = ClauseSetToCNF( fseq )
      //      println( nLine + nLine + "seq: "+seq)
      val f = seq.antecedent.head
      if ( !mapCLsym.contains( f.asInstanceOf[SchemaFormula] ) )
        if ( seq.succedent.isEmpty )
          mapCLsym = mapCLsym.updated( f.asInstanceOf[SchemaFormula], List.empty[SchemaFormula] )
        else
          mapCLsym = mapCLsym.updated( f.asInstanceOf[SchemaFormula], seq.succedent.head.asInstanceOf[SchemaFormula] :: Nil )
      else {
        val l = mapCLsym.get( f.asInstanceOf[SchemaFormula] ).get
        if ( seq.succedent.isEmpty )
          mapCLsym = mapCLsym.updated( f.asInstanceOf[SchemaFormula], l )
        else
          mapCLsym = mapCLsym.updated( f.asInstanceOf[SchemaFormula], seq.succedent.head.asInstanceOf[SchemaFormula] :: l )
      }
    } )
    mapCLsym
  }

  def apply( ccs: List[HOLSequent] ): List[HOLSequent] = {
    combiningCLsymbols( ccs )
    mapCLsym.toList.map( pair => HOLSequent( pair._1 :: Nil, And( pair._2.asInstanceOf[List[SchemaFormula]] ) :: Nil ) )
  }
}

object RW {
  //non-grounded map : CL_k -> Schemaformula
  def createMMap( ccs: List[HOLSequent] ): MMap[SchemaFormula, SchemaFormula] = {
    var map = MMap.empty[SchemaFormula, SchemaFormula]
    ccs.foreach( fseq => {
      if ( fseq.antecedent.size > 0 )
        map = map.updated( fseq.antecedent.head.asInstanceOf[SchemaFormula], fseq.succedent.head.asInstanceOf[SchemaFormula] )
    } )
    map
  }

  def rewriteGroundFla( f: SchemaFormula, map: MMap[SchemaFormula, SchemaFormula] ): SchemaFormula = {
    f match {
      case IndexedPredicate( ipred, l ) => {
        if ( l.head == IntZero() )
          return map.get( f.asInstanceOf[SchemaFormula] ).get
        else {
          val k = IntVar( "k" )
          val from = IndexedPredicate( ipred.name, Succ( k ) )
          val to = map.get( from ).get
          val new_map = Map.empty[Var, IntegerTerm] + Tuple2( IntVar( "k" ), Pred( l.head.asInstanceOf[IntegerTerm] ) )
          val subst = SchemaSubstitution( new_map ) //this was once a SchemaSubstitutionCNF, the normal substitution could make trouble here
          return rewriteGroundFla( subst( to ), map )
        }
      }
      case Or( l, r )  => Or( rewriteGroundFla( l, map ), rewriteGroundFla( r, map ) )
      case And( l, r ) => And( rewriteGroundFla( l, map ), rewriteGroundFla( r, map ) )
      case Neg( l )    => Neg( rewriteGroundFla( l, map ) )
      case _           => f
    }
  }
}

object CNFtoSet {
  //f should be in CNF
  def apply( f: SchemaFormula ): List[SchemaFormula] = {
    f match {
      case And( f1, f2 ) => apply( f1 ) ::: apply( f2 )
      case _             => f :: Nil
    }
  }
}

