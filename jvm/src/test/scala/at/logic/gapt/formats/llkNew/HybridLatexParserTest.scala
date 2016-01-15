package at.logic.gapt.formats.llkNew

import at.logic.gapt.formats.llkNew.ast.LambdaAST
import at.logic.gapt.expr._
import org.specs2.mutable._

import scala.io.Source

/**
 * Created with IntelliJ IDEA.
 * User: marty
 * Date: 10/14/13
 * Time: 3:02 PM
 * To change this template use File | Settings | File Templates.
 */
class LLKTest extends Specification {
  val p1 =
    """\AX{T,MON(h_1,\alpha)}{MON(h_1,\alpha) }
      |\AX{ NOCC(h_1,\alpha,\sigma)}{NOCC(h_1,\alpha,\sigma)}
      |\EXR{}{ NOCC(h_1,\alpha,\sigma)}{(exists s NOCC(h_1,\alpha,s))}
      |\ANDR{T,MON(h_1,\alpha), NOCC(h_1,\alpha,\sigma)}{MON(h_1,\alpha) & (exists s NOCC(h_1,\alpha,s))}
      |\EXR{}{T,MON(h_1,\alpha), NOCC(h_1,\alpha,\sigma)}{(exists h (MON(h,\alpha) & (exists s NOCC(h,\alpha,s))))}
      |\ANDL{T, MON(h_1,\sigma) & NOCC(h_1,\sigma,x)}{(exists h (MON(h,\alpha) & (exists s NOCC(h,\alpha,s))))}
      |\EXL{}{T, (exists h (MON(h,\sigma) & NOCC(h,\sigma,x)))}{(exists h (MON(h,\alpha) & (exists s NOCC(h,\alpha,s))))}
      |\ALLL{}{T, (all n exists h (MON(h,n) & NOCC(h,n,x)))}{(exists h (MON(h,\alpha) & (exists s NOCC(h,\alpha,s))))}
      |\DEF{T,A(\sigma)}{(exists h (MON(h,\alpha) & (exists s NOCC(h,\alpha,s))))}
      |\ALLR{}{T,A(\sigma)}{(all n exists h (MON(h,n) & (exists s NOCC(h,n,s))))}
      |\DEF{T,A(\sigma)}{C}
      |\CONTINUEWITH{\rho(\sigma)}
      |""".stripMargin

  def checkformula( f: String ) = {
    LLKProofParser.parseAll( LLKProofParser.formula, f ) match {
      case LLKProofParser.Success( r, _ ) =>
        ok( r.toString )
      case LLKProofParser.NoSuccess( msg, input ) =>
        ko( "Error at " + input.pos + ": " + msg )
    }
  }

  def llkFromClasspath( filename: String ) =
    LLKProofParser.parseString( Source.fromInputStream( getClass.getClassLoader getResourceAsStream filename ).mkString )

  "Hybrid Latex-GAPT" should {
    "correctly handle latex macros in formulas (1)" in {
      checkformula( "\\benc{j_1<n+1}" )
      ok
    }

    "correctly handle latex macros in formulas (2)" in {
      checkformula( "\\ite{\\benc{j_1<n+1}}{h'(j_1)}{\\alpha}" )
      ok
    }

    "correctly handle latex macros in formulas (3)" in {
      checkformula( "\\ite{\\ienc{j_1<n+1}}{h'(j_1)}{\\alpha}" )
      ok
    }

    "correctly handle latex macros in formulas (4)" in {
      checkformula( "\\ite{\\benc{j_1<n+1}}{h'(j_1)}{\\alpha} = 0" )
      ok
    }

    "accept the proof outline" in {
      //println(p1)
      LLKProofParser.parseAll( LLKProofParser.rules, p1 ) match {
        case LLKProofParser.Success( r: List[Token], _ ) =>
          //println(r)
          val lterms: List[LambdaAST] = r.flatMap( _ match {
            case RToken( _, _, a, s, _ ) => a ++ s
            case TToken( _, _, _ )       => Nil
            case AToken( _, _, a, s )    => a ++ s
          } )

          //println(lterms.flatMap(_.varnames).toSet)

          ok( "successfully parsed " + r )
        case LLKProofParser.NoSuccess( msg, input ) =>
          ko( "parsing error at " + input.pos + ": " + msg )
      }
      ok
    }

    "accept the proof outline with the parse interface" in {
      val r = LLKProofParser.parse( p1 )
      ok
    }

    "correctly infer replacement terms in equalities" in {
      import at.logic.gapt.proofs.lkOld.EquationVerifier.{ Different, Equal, EqualModuloEquality, checkReplacement }
      val List( a ) = List( "a" ) map ( x => Const( x, Ti ) )
      val List( f, g ) = List( "f", "g" ) map ( x => Const( x, Ti -> Ti ) )
      val List( p ) = List( "p" ) map ( x => Const( x, Ti -> ( Ti -> ( Ti -> To ) ) ) )
      val t1 = App( p, List( App( f, a ), App( f, App( g, App( f, a ) ) ), a ) )
      val t2 = App( p, List( App( f, a ), App( f, App( g, App( g, a ) ) ), a ) )
      val fa = App( f, a )
      val ga = App( g, a )

      checkReplacement( fa, ga, t1, t2 ) match {
        case Equal     => ko( "Terms " + t1 + " and " + t2 + " considered as equal, but they differ!" )
        case Different => ko( "Terms " + t1 + " and t2 considered as (completely) different, but they differ only modulo one replacement!" )
        case EqualModuloEquality( path ) =>
          //println("Path:"+path)
          ok
      }

      checkReplacement( fa, ga, t1, t1 ) match {
        case Equal                       => ok
        case Different                   => ko( "Terms " + t1 + " and t2 considered as (completely) different, but they are equal!" )
        case EqualModuloEquality( path ) => ko( "Found an equality modulo " + Eq( fa.asInstanceOf[LambdaExpression], ga.asInstanceOf[LambdaExpression] ) + " but should be equal!" )
      }
      ok
    }

    "load the simple example from file and parse it" in {
      val p = llkFromClasspath( "simple.llk" )
      //println(p)

      ok
    }

    "load the commutativity of + proof from file and parse it" in {
      val p = llkFromClasspath( "komm.llk" )
      ( p.proof( "THEPROOF" ) ) must not throwAn () //exception

      ok
    }

    "load the 3-2 pigeon hole example from file and parse it" in {
      val p = llkFromClasspath( "pigeon32.llk" )
      ( p.proof( "PROOF" ) ) must not throwAn () //exception

      ok
    }

    "load the tape3 proof from file" in {
      val p = llkFromClasspath( "tape3.llk" )
      p.proofs.length must be_>( 0 )
      p.Definitions.toList.length must be_>( 0 )
      p.axioms.length must be_>( 0 )
      ok
    }

  }

  "Tactics" should {
    "correctly prove the instance of an axiom" in {
      val vmap = Map[String, Ty]( "x" -> Ti, "y" -> Ti, "z" -> Ti )
      val cmap = Map[String, Ty]( "a" -> Ti, "1" -> Ti, "+" -> ( Ti -> ( Ti -> Ti ) ) )
      val naming: String => LambdaExpression = x => {
        if ( vmap contains x ) Var( x, vmap( x ) ) else
          Const( x, cmap( x ) )
      }
      val axiom = LLKFormulaParser.ASTtoHOL( naming, LLKProofParser.parseFormula( "(all x all y all z (x+(y+z)=(x+y)+z))" ) )
      val instance = LLKFormulaParser.ASTtoHOL( naming, LLKProofParser.parseFormula( "a+((1+x)+y)=(a+(1+x))+y" ) )
      val t1 = HOLFunction( Const( "+", Ti -> ( Ti -> Ti ) ), List(
        Const( "1", Ti ),
        Var( "x", Ti )
      ) )
      val t2 = Const( "a", Ti )
      val x = Var( "x", Ti )
      val y = Var( "y", Ti )
      val z = Var( "z", Ti )
      val sub = Substitution( List( ( x, t2 ), ( y, t1 ), ( z, y ) ) )
      val p = LLKProofParser.proveInstance( axiom.asInstanceOf[HOLFormula], instance.asInstanceOf[HOLFormula], sub )
      p.endSequent.formulas must haveSize( 2 )
      p.endSequent.antecedent must haveSize( 1 )
      p.endSequent.succedent must haveSize( 1 )
      p.endSequent.antecedent( 0 ) mustEqual ( axiom )
      p.endSequent.succedent( 0 ) mustEqual ( instance )
    }
  }
}
