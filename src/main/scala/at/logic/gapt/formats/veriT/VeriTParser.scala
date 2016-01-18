package at.logic.gapt.formats.veriT

import at.logic.gapt.expr.BetaReduction._
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLMatchingAlgorithm
import at.logic.gapt.expr.hol.{ removeQuantifiers, instantiate, isPrenex }
import at.logic.gapt.proofs.expansion._
import java.io.{ Reader, FileReader }
import scala.collection.immutable.HashMap
import scala.util.parsing.combinator._

class VeriTParserException( msg: String ) extends Exception( msg: String )
class VeriTUnfoldingTransitivityException( msg: String ) extends Exception( msg: String )

object VeriTParser extends RegexParsers {

  type Instances = ( FOLFormula, List[FOLFormula] )

  val nLine = sys.props( "line.separator" )

  def getEqReflInstances( f: List[FOLFormula] ): Instances = {
    val x = FOLVar( "x" )
    val eq_refl = All( x, Eq( x, x ) )
    ( eq_refl, f )
  }

  // Assuming all the antecedents of the implication are ordered:
  // ( =(x0, x1)  ^  =(x1, x2)  ^ ... ^  =(xn-1, xn)  ->  =(x0, xn) )
  // in veriT is *always* ( not =(x0, x1) , not =(x1, x2) , ... , not =(xn-1, xn) , =(x0, xn) )
  def getEqTransInstances( l: List[FOLFormula] ): Instances = {
    val x = FOLVar( "x" )
    val y = FOLVar( "y" )
    val z = FOLVar( "z" )
    val eq1 = Eq( x, y )
    val eq2 = Eq( y, z )
    val eq3 = Eq( x, z )
    val imp = Imp( And( eq1, eq2 ), eq3 )
    val eq_trans = All( x, All( y, All( z, imp ) ) )

    // Transforms a transitivity chain (represented as a list):
    //
    // [ not =(x0, x1) , not =(x1, x2) , ... , not =(xn-1, xn) , =(x0, xn) ]
    //
    // into simple transitivity formulas:
    //
    // =(x0, x1) ^ =(x1, x2) -> =(x0, x2)
    // =(x0, x2) ^ =(x2, x3) -> =(x0, x3)
    // ...
    // =(x0, xn-1) ^ =(xn-1, xn) -> =(x0, xn)
    //
    def unfoldChain( l: List[FOLFormula] ) = unfoldChain_( l.tail, l( 0 ) )
    def unfoldChain_( l: List[FOLFormula], c: FOLFormula ): List[FOLFormula] = l.head match {
      case Neg( Eq( x0, x1 ) ) => c match {
        // Note that the variables are:
        // x2=x3 ^ x0=x1
        // Checking all possible cases of atom ordering:

        // x=y ^ y=z -> x=z
        case Neg( Eq( x2, x3 ) ) if x3 == x0 =>
          val newc = Neg( Eq( x2, x1 ) )
          // Instances
          val f1 = instantiate( eq_trans, x2 )
          val f2 = instantiate( f1, x0 ) // or x3, should be the same
          val f3 = instantiate( f2, x1 )

          f3 :: unfoldChain_( l.tail, newc )

        // x=y ^ z=y -> x=z
        case Neg( Eq( x2, x3 ) ) if x3 == x1 =>
          val newc = Neg( Eq( x2, x0 ) )
          // Instances
          val f1 = instantiate( eq_trans, x2 )
          val f2 = instantiate( f1, x1 ) // or x3, should be the same
          val f3 = instantiate( f2, x0 )

          f3 :: unfoldChain_( l.tail, newc )

        // y=x ^ z=y -> x=z
        case Neg( Eq( x2, x3 ) ) if x2 == x1 =>
          val newc = Neg( Eq( x3, x0 ) )
          // Instances
          val f1 = instantiate( eq_trans, x3 )
          val f2 = instantiate( f1, x1 ) // or x2, should be the same
          val f3 = instantiate( f2, x0 )

          f3 :: unfoldChain_( l.tail, newc )

        // y=x ^ y=z -> x=z
        case Neg( ( Eq( x2, x3 ) ) ) if x2 == x0 =>
          val newc = Neg( Eq( x3, x1 ) )
          // Instances
          val f1 = instantiate( eq_trans, x3 )
          val f2 = instantiate( f1, x0 ) // or x2, should be the same
          val f3 = instantiate( f2, x1 )

          f3 :: unfoldChain_( l.tail, newc )

        case Neg( ( Eq( x2, x3 ) ) ) =>
          throw new VeriTUnfoldingTransitivityException( "ERROR: the conclusion of the previous terms have" +
            " no literal in common with the next one. Are the literals out of order?" +
            nLine + "conclusion: " + c + nLine + "second literal: " + l.head )

        case _ =>
          throw new VeriTUnfoldingTransitivityException( "ERROR: wrong format for negated equality: " + c )
      }

      // When reaching the final literal, check if they are the same.
      case Eq( x0, x1 ) => c match {
        case Neg( Eq( x2, x3 ) ) if x0 == x2 && x1 == x3 => Nil
        case Neg( Eq( x2, x3 ) ) if x1 == x2 && x0 == x3 => Nil

        case Neg( Eq( x2, x3 ) ) =>
          throw new VeriTUnfoldingTransitivityException( "ERROR: the conclusion of the previous terms" +
            " have no literal in common with the conclusion of the chain. Are the literals out of order?" +
            " Is the conclusion not the last one?" )

        case _ =>
          throw new VeriTUnfoldingTransitivityException( "ERROR: wrong format for negated equality: " + c )
      }

      case _ =>
        throw new VeriTUnfoldingTransitivityException( "Unmatched list head: " + l.head )
    }

    val instances = unfoldChain( l )
    ( eq_trans, instances )
  }

  // Assuming all the antecedents of the implication are ordered:
  // ( =(x0, y0)  ^  =(x1, y1)  ^ ... ^  =(xn, yn)  ->  =(f x0...xn, f y0...yn) )
  // in veriT is *always* ( not =(x0, y0) , not =(x1, y1) , ... , not =(xn, yn), =(f x0...xn, f y0...yn) )
  def getEqCongrInstances( f: List[FOLFormula] ): Instances = {

    def getFunctionName( f: FOLFormula ): String = f match {
      case Eq( f1, _ ) => f1 match {
        case FOLFunction( n, _ ) => n.toString
      }
    }

    def getArgsLst( f: FOLFormula ) = f match {
      case Eq( f1, f2 ) => ( f1, f2 ) match {
        case ( FOLFunction( _, args1 ), FOLFunction( _, args2 ) ) => ( args1, args2 )
      }
    }

    // Generate the eq_congruent formula with the right number of literals
    def gen_eq_congr( n: Int, fname: String ): FOLFormula = {
      val listX = ( for { i <- 1 to n } yield FOLVar( "x" + i ) ).toList
      val listY = ( for { i <- 1 to n } yield FOLVar( "y" + i ) ).toList
      val equalities = ( listX, listY ).zipped map ( Eq( _, _ ) )
      val conj = And( equalities )
      val name = fname
      val f1 = FOLFunction( name, listX )
      val f2 = FOLFunction( name, listY )
      val last_eq = Eq( f1, f2 )
      val matrix = Imp( conj, last_eq )

      val quantY = listY.foldRight( matrix ) {
        case ( yi, f ) => All( yi, f )
      }

      listX.foldRight( quantY ) {
        case ( xi, f ) => All( xi, f )
      }
    }

    val fname = getFunctionName( f.last )
    val n = getArgsLst( f.last )._1.size
    val eq_congr = gen_eq_congr( n, fname )

    val ( args1, args2 ) = getArgsLst( f.last )
    val eqs_correct = ( args1, args2 ).zipped map ( Eq( _, _ ) )
    val instance = Imp( And( eqs_correct ), f.last )

    ( eq_congr, List( instance ) )
  }

  // Assuming all the antecedents of the implication are ordered:
  // ( =(x0, y0)  ^  =(x1, y1)  ^ ... ^  =(xn, yn) ^ p(x0...xn)  ->  p(y0...yn) )
  // in veriT is *always* 
  // ( not =(x0, y0) , not =(x1, y1) , ... , not =(xn, yn), not p(x0...xn), p(y0...yn) )
  // or
  // ( not =(x0, y0) , not =(x1, y1) , ... , not =(xn, yn), p(x0...xn), not p(y0...yn) )
  def getEqCongrPredInstances( f: List[FOLFormula] ): Instances = {

    def getPredName( f: FOLFormula ): String = f match {
      case FOLAtom( p, _ )        => p.toString
      case Neg( FOLAtom( p, _ ) ) => p.toString
    }

    def getArgsLst( p1: FOLFormula, p2: FOLFormula ) = ( p1, p2 ) match {
      case ( Neg( FOLAtom( _, args1 ) ), FOLAtom( _, args2 ) ) => ( args1, args2 )
      case ( FOLAtom( _, args1 ), Neg( FOLAtom( _, args2 ) ) ) => ( args2, args1 )
    }

    // Generate the eq_congruent_pred with the right number of literals
    def gen_eq_congr_pred( n: Int, pname: String ): FOLFormula = {
      val listX = ( for { i <- 1 to n } yield FOLVar( "x" + i ) ).toList
      val listY = ( for { i <- 1 to n } yield FOLVar( "y" + i ) ).toList
      val equalities = ( listX, listY ).zipped map ( Eq( _, _ ) )
      val name = pname
      val p1 = FOLAtom( name, listX )
      val p2 = FOLAtom( name, listY )
      val conj = And( equalities :+ p1 )
      val matrix = Imp( conj, p2 )

      val quantY = listY.foldRight( matrix ) {
        case ( yi, f ) => All( yi, f )
      }

      listX.foldRight( quantY ) {
        case ( xi, f ) => All( xi, f )
      }
    }

    val pname = getPredName( f.last )
    val n = getArgsLst( f( f.length - 2 ), f( f.length - 1 ) )._1.size
    val eq_congr_pred = gen_eq_congr_pred( n, pname )

    val ( args1, args2 ) = getArgsLst( f( f.length - 2 ), f( f.length - 1 ) )
    val eqs_correct = ( args1, args2 ).zipped map ( Eq( _, _ ) )
    val ( p1, p2 ) = ( f( f.length - 2 ), f( f.length - 1 ) ) match {
      case ( Neg( f1 ), f2 ) => ( f1, f2 )
      case ( f1, Neg( f2 ) ) => ( f2, f1 )
    }
    val instance = Imp( And( eqs_correct :+ p1 ), p2 )

    ( eq_congr_pred, List( instance ) )
  }

  def getExpansionProof( filename: String ): Option[ExpansionSequent] = {
    getExpansionProof( new FileReader( filename ) )
  }

  def getExpansionProofWithSymmetry( fileName: String ): Option[ExpansionSequent] =
    getExpansionProof( fileName ) map { addSymmetry( _ ) }

  // NOTE: The expansion proof returned is a tautology modulo symmetry!!!!
  def getExpansionProof( reader: Reader ): Option[ExpansionSequent] = {
    parseAll( proof, reader ) match {
      case Success( r, _ ) => r
      case Failure( msg, next ) =>
        throw new VeriTParserException( "VeriT parsing: syntax failure " + msg + nLine + "at line " + next.pos.line + " and column " + next.pos.column )
      case Error( msg, next ) =>
        throw new VeriTParserException( "VeriT parsing: syntax error " + msg + nLine + "at line " + next.pos.line + " and column " + next.pos.column )
    }
  }

  def isUnsat( filename: String ): Boolean = isUnsat( new FileReader( filename ) )

  def isUnsat( reader: Reader ): Boolean = {
    parseAll( parseUnsat, reader ) match {
      case Success( r, _ ) => r
      case Failure( msg, next ) =>
        throw new VeriTParserException( "VeriT parsing: syntax failure " + msg + nLine + "at line " + next.pos.line + " and column " + next.pos.column )
      case Error( msg, next ) =>
        throw new VeriTParserException( "VeriT parsing: syntax error " + msg + nLine + "at line " + next.pos.line + " and column " + next.pos.column )
    }
  }

  // Each list of formulas corresponds to the formulas occurring in one of the axioms.
  // Assuming all the input and input processing rules occur before the resolution steps (i.e. the proof itself).
  def proof: Parser[Option[ExpansionSequent]] = rep( header ) ~> rep( preprocess ) ~ rep( rules ) ^^ {

    // Relying on the fact that if the formula is unsatisfiable, a proof is
    // always printed. If there is no proof, the result is sat.
    case Nil ~ Nil => None

    case pp ~ r =>

      val preamblemap = pp.foldLeft( Map[String, List[FOLFormula]]() )( ( acc, p ) => acc + p )
      val usedclauses = r.foldLeft( List[String]() )( ( acc, p ) => acc ++ p._1 ).distinct

      val input = preamblemap.foldLeft( List[FOLFormula]() ) {
        case ( acc, p ) =>
          if ( usedclauses.contains( p._1 ) ) {
            acc ++ p._2
          } else acc
      }

      val axioms = r.map( p => p._2 ).flatten

      // Join the instances of the same quantified formula
      val keys = axioms.map( p => p._1 ).distinct
      val joinedInst = keys.foldLeft( List[Instances]() ) {
        case ( acc, f ) =>
          val keyf = axioms.filter( p => p._1 == f )
          val allInst = keyf.foldLeft( List[FOLFormula]() )( ( acc, p ) => p._2 ++ acc )
          ( f, allInst.distinct ) :: acc
      }

      // Transform all pairs into expansion trees
      val inputET = input.map( p => formulaToExpansionTree( p, false ) )
      val axiomET = joinedInst.map {
        case p =>
          // Match p._1 and p._2 to get the variable mapping
          assert( isPrenex( p._1 ) )
          val fMatrix = removeQuantifiers( p._1 )
          val instances = p._2
          val subs = instances.foldLeft( List[FOLSubstitution]() ) {
            case ( lst, instance ) =>
              FOLMatchingAlgorithm.matchTerms( fMatrix, instance ) match {
                case Some( s ) => s :: lst
                case None      => lst
              }
          }
          formulaToExpansionTree( p._1, subs, false )
      }
      val ant = axiomET ++ inputET

      val cons = List()
      Some( new ExpansionSequent( ant.toSeq, cons.toSeq ) )
  }

  def parseUnsat: Parser[Boolean] = title ~ rep( success ) ~> ( unsat ^^ { case s => true } | sat ^^ { case s => false } ) <~ success

  def label: Parser[String] = ".c" ~ """\d+""".r ^^ { case s1 ~ s2 => s1 ++ s2 }

  // FILE HEADER
  def header: Parser[String] = success | unsat | sat | title | msg
  def success: Parser[String] = "success"
  def unsat: Parser[String] = "unsat"
  def sat: Parser[String] = "sat"
  def title: Parser[String] = """veri(.*)\.""".r
  def msg: Parser[String] = "Formula is Satisfiable"

  // INPUT PROCESSING RULES
  def preprocess: Parser[( String, List[FOLFormula] )] = "(set" ~> label ~ "(" ~ rulePreProc <~ "))" ^^ { case l ~ "(" ~ r => ( l, r ) }
  def rulePreProc: Parser[List[FOLFormula]] = input | tmp_distinct_elim | tmp_alphaconv | tmp_let_elim
  def input: Parser[List[FOLFormula]] = "input" ~> conclusion
  def tmp_distinct_elim: Parser[List[FOLFormula]] = "tmp_distinct_elim" ~ premises ~> conclusion
  def tmp_alphaconv: Parser[List[FOLFormula]] = "tmp_alphaconv" ~ premises ~> conclusion
  def tmp_let_elim: Parser[List[FOLFormula]] = "tmp_let_elim" ~ premises ~> conclusion

  // RESOLUTION RULES AND EQUALITY AXIOMS
  // Inner rules return the labels of the clauses used and equality axioms returns the axiom and its instances
  def rules: Parser[( List[String], Option[Instances] )] = "(set" ~ label ~ "(" ~> rule <~ "))"
  def rule: Parser[( List[String], Option[Instances] )] = eqAxiom ^^ { case i => ( Nil, Some( i ) ) } | innerRule ^^ { case s => ( s, None ) }
  def eqAxiom: Parser[Instances] = eq_reflexive | eq_transitive | eq_congruence | eq_congruence_pred
  def eq_reflexive: Parser[Instances] = "eq_reflexive" ~> conclusion ^^ {
    case c =>
      getEqReflInstances( c )
  }
  def eq_transitive: Parser[Instances] = "eq_transitive" ~> conclusion ^^ {
    case c =>
      getEqTransInstances( c )
  }
  def eq_congruence: Parser[Instances] = "eq_congruent" ~> conclusion ^^ {
    case c =>
      getEqCongrInstances( c )
  }
  def eq_congruence_pred: Parser[Instances] = "eq_congruent_pred" ~> conclusion ^^ {
    case c =>
      getEqCongrPredInstances( c )
  }

  def innerRule: Parser[List[String]] = resolution | and | and_pos | and_neg | or | or_pos | or_neg | implies | implies_pos | implies_neg1 | implies_neg2 | not_implies1 | not_implies2 | not_and | not_or | equiv1 | equiv2 | true_ | false_
  // Rules that I don't care except if they use some clause (collecting their labels)
  def resolution: Parser[List[String]] = "resolution" ~> premises <~ conclusion
  def and: Parser[List[String]] = "and" ~> premises <~ conclusion
  def and_pos: Parser[List[String]] = "and_pos" ~> conclusion ^^ { case _ => Nil }
  def and_neg: Parser[List[String]] = "and_neg" ~> conclusion ^^ { case _ => Nil }
  def or: Parser[List[String]] = "or" ~> premises <~ conclusion
  def or_pos: Parser[List[String]] = "or_pos" ~> conclusion ^^ { case _ => Nil }
  def or_neg: Parser[List[String]] = "or_neg" ~> conclusion ^^ { case _ => Nil }
  def implies: Parser[List[String]] = "implies" ~> premises <~ conclusion
  def implies_pos: Parser[List[String]] = "implies_pos" ~> conclusion ^^ { case _ => Nil }
  def implies_neg1: Parser[List[String]] = "implies_neg1" ~> conclusion ^^ { case _ => Nil }
  def implies_neg2: Parser[List[String]] = "implies_neg2" ~> conclusion ^^ { case _ => Nil }
  def not_implies1: Parser[List[String]] = "not_implies1" ~> premises <~ conclusion
  def not_implies2: Parser[List[String]] = "not_implies2" ~> premises <~ conclusion
  def not_and: Parser[List[String]] = "not_and" ~> premises <~ conclusion
  def not_or: Parser[List[String]] = "not_or" ~> premises <~ conclusion
  def equiv1: Parser[List[String]] = "equiv1" ~> premises <~ conclusion
  def equiv2: Parser[List[String]] = "equiv2" ~> premises <~ conclusion
  def true_ = "true" ~> conclusion ^^ { _ => Nil }
  def false_ = "false" ~> conclusion ^^ { _ => Nil }

  // Collecting the clauses' labels used in the proof
  def premises: Parser[List[String]] = ":clauses (" ~> rep( label ) <~ ")"
  def conclusion: Parser[List[FOLFormula]] = ":conclusion (" ~> rep( expression ) <~ ")"

  def expression: Parser[FOLFormula] = formula | let
  def formula: Parser[FOLFormula] = andFormula | orFormula | notFormula | implFormula | pred

  def term: Parser[FOLTerm] = variable | constant | function
  def variable: Parser[FOLTerm] = var_name ^^ { case n => FOLVar( n ) }
  def constant: Parser[FOLTerm] = name ^^ { case n => FOLConst( n ) }
  def function: Parser[FOLTerm] = "(" ~> name ~ rep( term ) <~ ")" ^^ {
    case name ~ args =>
      val n = name
      FOLFunction( n, args )
  }

  def andFormula: Parser[FOLFormula] = "(and" ~> rep( formula ) <~ ")" ^^ {
    case flst => And( flst )
  }
  def orFormula: Parser[FOLFormula] = "(or" ~> rep( formula ) <~ ")" ^^ {
    case flst => Or( flst )
  }
  def implFormula: Parser[FOLFormula] = "(=>" ~> rep( formula ) <~ ")" ^^ {
    case flst =>
      val last = flst( flst.size - 1 )
      val second_last = flst( flst.size - 2 )
      val rest = flst.dropRight( 2 )
      val imp = Imp( second_last, last )
      rest.foldRight( imp ) { case ( f, acc ) => Imp( f, acc ) }
  }
  def notFormula: Parser[FOLFormula] = "(not" ~> formula <~ ")" ^^ {
    case f => Neg( f )
  }
  def pred: Parser[FOLFormula] = "(" ~> name ~ rep( term ) <~ ")" ^^ {
    case name ~ args =>
      FOLAtom( name, args )
  } | name ^^ {
    // No parenthesis around unary symbols
    case name => FOLAtom( name, Nil )
  }

  // Syntax of let-expressions:
  // (let (v1 t1) ... (vn tn) exp)
  // which is equivalent to the lambda-expression:
  // (\lambda v1 ... vn exp) t1 ... tn
  // But we are not constructing the terms for now, first because we don't need 
  // it and second because the garbage collector goes crazy and crashes while
  // constructing this huge lambda-term
  def let: Parser[FOLFormula] = "(" ~> "let" ~> "(" ~> rep( binding ) ~ ")" ~ expression <~ ")" ^^ {
    case _ => Or( List() )
  }

  def binding: Parser[( FOLTerm, FOLTerm )] = "(" ~> constant ~ term <~ ")" ^^ {
    case v ~ t => ( v, t )
  }

  def name: Parser[String] = """[^ ():$]+""".r
  // FIXME: this is a hack to read variables generated by VeriTExporter
  def var_name: Parser[String] = """[^ ():$]+""".r <~ "$"

}
