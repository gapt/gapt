import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import at.logic.gapt.expr._
import at.logic.gapt.cutintro.{MaxSATMethod, CutIntroduction}
import at.logic.gapt.provers.maxsat.ExternalMaxSATSolver
import at.logic.gapt.provers.sat.MiniSAT
import at.logic.gapt.provers.veriT.VeriT

val C = parseFormula( "(all x all y f(x,y) = f(y,x))" )
val AS = parseFormula( "(all u all v ( f(u,v)=u -> ( f(v,u)=v -> u=v )))" )

val A = parseFormula( "(all x all y all z f(f(x,y),z) = f(x,f(y,z)))" )
val Tpo = parseFormula( "(all x all y all z ( f(x,y)=x -> ( f(y,z)=y -> f(x,z)=x )))" )

def trans = {
  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )
  val x0 = FOLVar( "x_0" )
  val y0 = FOLVar( "y_0" )
  val z0 = FOLVar( "z_0" )

  val A0 = parseFormula( "f(f(x_0,y_0),z_0) = f(x_0,f(y_0,z_0))" )
  val A1 = parseFormula( "(all z f(f(x_0,y_0),z) = f(x_0,f(y_0,z)))" )
  val A2 = parseFormula( "(all y all z f(f(x_0,y),z) = f(x_0,f(y,z)))" )
  val T0 = parseFormula( "f(x_0,y_0)=x_0 -> ( f(y_0,z_0)=y_0 -> f(x_0,z_0)=x_0 )" )
  val T1 = parseFormula( "(all z ( f(x_0,y_0)=x_0 -> ( f(y_0,z)=y_0 -> f(x_0,z)=x_0 )))" )
  val T2 = parseFormula( "(all y all z ( f(x_0,y)=x_0 -> ( f(y,z)=y -> f(x_0,z)=x_0 )))" )
  val s = HOLSequent( List( A0 ), List( T0 ))

  val E = VeriT.getExpansionSequent( s ).get
  val Emin = minimalExpansionSequents( E, MiniSAT )
  if ( Emin.size != 1 ) println( "WARNING: trans expansion sequent not minimal" )

  val p0 = ExpansionProofToLK( E )
  val p1 = ForallLeftRule( p0, A1, z0 )
  val p2 = ForallLeftRule( p1, A2, y0 )
  val p3 = ForallLeftRule( p2, A, x0 )
  val p4 = ForallRightRule( p3, T1, z0 )
  val p5 = ForallRightRule( p4, T2, y0 )
  ForallRightRule( p5, Tpo, x0 )
}

def antisymm = {
  val u0 = FOLVar( "u_0" )
  val v0 = FOLVar( "v_0" )

  val C0 = parseFormula( "f(u_0,v_0) = f(v_0,u_0)" )
  val AS0 = parseFormula( "f(u_0,v_0)=u_0 -> ( f(v_0,u_0)=v_0 -> u_0=v_0 )" )
  val s = HOLSequent( List( C0 ), List( AS0 ))

  val E = VeriT.getExpansionSequent( s ).get
  val Emin = minimalExpansionSequents( E, MiniSAT )
  if ( Emin.size != 1 ) println( "WARNING: antisymm expansion sequent not minimal" )

  val p0 = ExpansionProofToLK( E )
  val p1 = ForallLeftRule( p0, parseFormula( "(all v f(u_0,v) = f(v,u_0) )" ), v0 )
  val p2 = ForallLeftRule( p1, C, u0 )
  val p3 = ForallRightRule( p2, parseFormula( "(all v ( f(u_0,v)=u_0 -> ( f(v,u_0)=v -> u_0=v )))" ), v0 )
  ForallRightRule( p3, AS, u0 )
}

def lhs = {
  ContractionMacroRule( AndRightRule( antisymm, AS, trans, Tpo ))
}

def rhs = {
  val u = FOLVar( "u" )
  val v = FOLVar( "v" )
  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )
  val a = FOLConst( "a" )
  val b = FOLConst( "b" )
  val c = FOLConst( "c" )

  val s1 = FOLSubstitution( Map( (u,a), (v,b) ) ) //val AS1 = parseFormula( "( f(a,b)=a -> ( f(b,a)=b -> a=b ))" )
  val s2 = FOLSubstitution( Map( (u,b), (v,c) ) ) //val AS2 = parseFormula( "( f(b,c)=b -> ( f(c,b)=c -> b=c ))" )
  val EAS = formulaToExpansionTree( AS, s1::s2::Nil, false )

  val t1 = FOLSubstitution( Map( (x,b), (y,c), (z,a) ) ) //val Tpo1 = parseFormula( "( f(b,c)=b -> ( f(c,a)=c -> f(b,a)=b ))" )
  val t2 = FOLSubstitution( Map( (x,c), (y,a), (z,b) ) ) //val Tpo2 = parseFormula( "( f(c,a)=c -> ( f(a,b)=a -> f(c,b)=c ))" )
  val ETpo = formulaToExpansionTree( Tpo, t1::t2::Nil, false )

  val ETcut = ETAnd( EAS, ETpo )
  val conc = parseFormula( "( f(a,b)=a & f(b,c)=b & f(c,a)=c ) -> ( a=b & b=c )" )
  val Econc = formulaToExpansionTree( conc, true )

  val E = ExpansionSequent( ETcut::Nil, Econc::Nil )
  ExpansionProofToLK( E )
}

// proof with cut
def pwc = {
  CutRule( lhs, rhs, And( AS, Tpo ))
}

val p = ReductiveCutElimination( pwc )
val (terms, encoding) = FOLInstanceTermEncoding(p)

// This does not work, even running it for 2 days produces only a grammar of size 22.
if (false) CutIntroduction.compressLKProof(p,
  method = MaxSATMethod(new ExternalMaxSATSolver("open-wbo", "-cpu-lim=30", "-algorithm=1"), 3),
  verbose = true)
