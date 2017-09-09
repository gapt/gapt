package at.logic.gapt.formats.lean

import java.io.IOException

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.universalClosure
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.proofs.lk.{ LKProof, freeVariablesLK }
import at.logic.gapt.utils.{ ExternalProgram, NameGenerator, runProcess, withTempFile }
import at.logic.gapt.proofs._

import scala.collection.mutable

// TODO: theory axioms, induction inferences

object LeanNames {
  type NameKind = Int
  val VAR = 0
  val CONST = 1
  val TY = 2
}
import LeanNames._
class LeanNames(
    val nameGenerator: NameGenerator                                       = new NameGenerator( Set() ),
    gapt2lean:         mutable.Map[( String, LeanNames.NameKind ), String] = mutable.Map() ) {
  def markUsed( leanName: String ): Unit = nameGenerator.fresh( leanName )
  def register( gaptName: String, kind: NameKind, leanName: String ): Unit = {
    require( !gapt2lean.contains( gaptName -> kind ) )
    gapt2lean( gaptName -> kind ) = leanName
    nameGenerator.fresh( leanName )
  }

  def getLeanName( gaptName: String, kind: NameKind ): String = gapt2lean.getOrElseUpdate( gaptName -> kind, {
    val withoutSymbols = gaptName.
      replace( "+", "_plus_" ).
      replace( "*", "_times_" ).
      replace( "/", "_div_" ).
      replace( ">", "_gt_" ).
      replace( "<", "_lt_" ).
      replace( ">=", "_ge_" ).
      replace( "<=", "_le_" ).
      replace( "=", "_eq_" ).
      replace( "⊃", "_imp_" ).
      replace( "∀", "_all_" ).
      replace( "__", "_" ).
      filter( c => c == '_' || Character.isAlphabetic( c ) || Character.isDigit( c ) ).
      dropWhile( _ == '_' ).
      reverse.dropWhile( _ == '_' ).reverse

    val beginsWithLetters =
      if ( withoutSymbols.isEmpty || !Character.isAlphabetic( withoutSymbols( 0 ) ) )
        "c_" + withoutSymbols
      else
        withoutSymbols

    nameGenerator.fresh( beginsWithLetters )
  } )

  def fork = new LeanNames( nameGenerator.fork, gapt2lean )
}

class LeanExporter {
  val nameMap = new LeanNames

  Seq(
    "gapt",
    "apply", "intros",
    "begin", "end", "def", "definition", "lemma", "theorem", // TODO: ...
    "implies",
    "list", "nil", "cons" ).foreach( nameMap.markUsed )

  val hypName = nameMap.nameGenerator.fresh( "hyp" ) + ".h_"
  val axiomNames = mutable.Map[HOLSequent, String]()

  def export( ty: Ty ): String = ty match {
    case TBase( name, params ) => ( nameMap.getLeanName( name, TY ) :: params.map( export ) ).mkString( " " )
    case TVar( _ )             => "_"
    case a -> b                => s"(${export( a )} -> ${export( b )})"
  }

  def exportBinder( sym: String, x: Var, sub: Expr ): String = {
    val x_ = nameMap.getLeanName( x.name, VAR )
    s"($sym $x_ : ${export( x.ty )}, ${export( sub )})"
  }

  def export( expr: Expr ): String = expr match {
    case All( x, sub ) => exportBinder( "∀", x, sub )
    case Ex( x, sub )  => exportBinder( "∃", x, sub )
    case Eq( x, y )    => s"(${export( x )} = ${export( y )})"
    case Imp( x, y )   => s"(${export( x )} -> ${export( y )})"
    case Apps( hd, as ) if as.nonEmpty =>
      s"(${export( hd )} ${as.map( export ).mkString( " " )})"
    case Abs( x, sub ) => exportBinder( "λ", x, sub )
    case Const( n, _ ) => nameMap.getLeanName( n, CONST )
    case Var( n, _ )   => nameMap.getLeanName( n, VAR )
  }

  def mkSequentFormula( sequent: HOLSequent ): Formula = sequent match {
    case Sequent( Seq(), Seq() )    => Bottom()
    case Sequent( Seq(), Seq( y ) ) => y
    case Sequent( Seq(), y +: ys ) =>
      y | mkSequentFormula( Sequent( Seq(), ys ) )
    case Sequent( x +: xs, ys ) =>
      x --> mkSequentFormula( Sequent( xs, ys ) )
  }

  def export( sequent: HOLSequent ): String = export( mkSequentFormula( sequent ) )

  def export( upd: Context.Update ): String = upd match {
    case Context.InductiveType( To, _ ) =>
      nameMap.register( "o", TY, "Prop" )
      nameMap.register( TopC.name, CONST, "true" )
      nameMap.register( BottomC.name, CONST, "false" )
      ""
    case Context.ConstDecl( c @ Const( "=", _ ) ) =>
      nameMap.register( c.name, CONST, "eq" ); ""
    case Context.ConstDecl( c @ NegC() ) =>
      nameMap.register( c.name, CONST, "not" ); ""
    case Context.ConstDecl( c @ AndC() ) =>
      nameMap.register( c.name, CONST, "and" ); ""
    case Context.ConstDecl( c @ OrC() ) =>
      nameMap.register( c.name, CONST, "or" ); ""
    case Context.ConstDecl( c @ ImpC() ) =>
      nameMap.register( c.name, CONST, "implies" ); ""
    case Context.ConstDecl( c @ ExistsC( _ ) ) =>
      nameMap.register( c.name, CONST, "Exists" )
      ""
    case Context.ConstDecl( c @ ForallC( _ ) ) =>
      val all = nameMap.getLeanName( c.name, CONST )
      s"def $all {a : Type} (P : a -> Prop) := ∀x, P x\n\n"
    case Context.Sort( sort ) =>
      s"constant ${nameMap.getLeanName( sort.name, TY )} : Type\n\n"
    case Definition( Const( n, ty ), by ) =>
      val what = nameMap.getLeanName( n, CONST )
      s"def $what : ${export( ty )} := ${export( by )}\n\n"
    //    case Context.Axiom( ax ) =>
    //      val axName = nameMap.nameGenerator.fresh( "ax" )
    //      axiomNames( ax ) = axName
    //      s"axiom $axName : ${export( universalClosure( mkSequentFormula( ax ) ) )}\n\n"
    case Context.ConstDecl( Const( n, t ) ) =>
      s"constant ${nameMap.getLeanName( n, CONST )} : ${export( t )}\n\n"
    case Context.InductiveType( ty, ctrs ) =>
      s"inductive ${nameMap.getLeanName( ty.name, TY )} : Type\n" +
        ctrs.map { case Const( n, t ) => s"| ${nameMap.getLeanName( n, CONST )} : ${export( t )}\n" }.mkString +
        s"open ${nameMap.getLeanName( ty.name, TY )}\n\n"
  }

  def export( p: LKProof ): String = {
    val out = new StringBuilder

    val fvParams = freeVariablesLK( p ).toSeq.sortBy( _.name )
      .map( v => s" (${nameMap.getLeanName( v.name, VAR )} : ${export( v.ty )})" ).mkString

    out ++= s"lemma ${nameMap.nameGenerator.fresh( "lk_proof" )}$fvParams : ${export( p.endSequent )} :=\n"
    out ++= "begin\n"

    val hs = p.endSequent.indicesSequent.map {
      case Ant( i ) => i
      case Suc( j ) => p.endSequent.antecedent.size + j
    }

    def mkHypNameList( is: Seq[Int] ): String = s"[${is.map( s"`$hypName" + _ ).mkString( ", " )}]"
    out ++= s"gapt.lk.sequent_formula_to_hyps ${mkHypNameList( hs.antecedent )} ${mkHypNameList( hs.succedent )},\n"

    import at.logic.gapt.proofs.lk._
    def f( p: LKProof, hs: Sequent[Int], hi: Int ): Unit = p match {
      case p: ContractionLeftRule  => f( p.subProof, p.getSequentConnector.parent( hs ), hi )
      case p: ContractionRightRule => f( p.subProof, p.getSequentConnector.parent( hs ), hi )
      case p: WeakeningLeftRule    => f( p.subProof, p.getSequentConnector.parent( hs ), hi )
      case p: WeakeningRightRule   => f( p.subProof, p.getSequentConnector.parent( hs ), hi )
      case p: DefinitionRule       => f( p.subProof, p.getSequentConnector.parent( hs ), hi )
      case _: ProofLink            => out ++= "exact sorry,\n"
      case _ =>
        var rule = s"gapt.lk.${p.longName}"
        p match {
          case p: CutRule =>
            rule += s" ${export( p.cutFormula )}"
          case WeakQuantifierRule( _, _, _, term, _, _ ) =>
            rule += s" ${export( term )}"
          case p: EqualityRule =>
            rule += ( if ( p.leftToRight ) "1" else "2" )
            rule += s" ${export( p.replacementContext )} ${export( p.what )} ${export( p.by )} $hypName${hs( p.eqInConclusion )}"
          case _ =>
        }
        for ( i <- p.mainIndices )
          rule += s" $hypName${hs( i )}"
        out ++= s"apply ($rule), "
        for ( ( q, occConn_, auxs_ ) <- ( p.immediateSubProofs, p.occConnectors, p.auxIndices ).zipped ) {
          val ( occConn, auxs ) = p match {
            case p: EqualityRule =>
              (
                occConn_.copy( parentsSequent = occConn_.parentsSequent.
                  updated( p.eqInConclusion, Seq( p.eq ) ).
                  updated( p.auxInConclusion, Seq( p.aux ) ) ),
                Seq( p.aux ) )
            case _ => ( occConn_, auxs_ )
          }
          val hs_ = auxs.zip( Stream.from( hi ) ).foldLeft( occConn.parent( hs, -1 ) )( ( hs_, ai ) => hs_.updated( ai._1, ai._2 ) )
          out ++= "intros"
          p match {
            case p: Eigenvariable =>
              out ++= s" ${nameMap.getLeanName( p.eigenVariable.name, VAR )}"
            case _ =>
          }
          for ( a <- auxs )
            out ++= s" $hypName${hs_( a )}"
          out ++= ",\n"
          f( q, hs_, math.max( ( hs_.elements :+ 0 ).max + 1, hi ) )
        }
    }
    f( p, hs, ( hs.elements :+ 0 ).max + 1 )

    out ++= "end\n"
    out.result()
  }

  def export( ctx: Context ): String =
    ctx.updates.reverse.map( export ).mkString

  def mkImport( includeDirectly: Boolean ): String =
    if ( includeDirectly )
      ClasspathInputFile( "lean/gapt.lean", getClass ).read
    else
      "import .gapt\n"

  def mkFile( includeDirectly: Boolean )( f: => String ): String =
    mkImport( includeDirectly ) +
      "noncomputable theory\n\n" +
      "namespace gapt_export\n\n" +
      f +
      "\nend gapt_export\n"
}
object LeanExporter {
  def apply( ctx: Context ): String = apply( ctx, includeDirectly = false )
  def apply( ctx: Context, includeDirectly: Boolean ): String = {
    val exporter = new LeanExporter
    exporter.mkFile( includeDirectly ) { exporter.export( ctx ) }
  }

  def apply( ctx: Context, p: LKProof ): String = apply( ctx, p, includeDirectly = false )
  def apply( ctx: Context, p: LKProof, includeDirectly: Boolean ): String = {
    val exporter = new LeanExporter
    exporter.mkFile( includeDirectly ) { exporter.export( ctx ) + exporter.export( p ) }
  }
}

object LeanChecker extends ExternalProgram {
  val executable = "lean"

  private val versionRegex = """Lean \(version ([0-9.]+),""".r.unanchored
  val version: String =
    try runProcess( Seq( "lean", "--version" ) ) match {
      case versionRegex( v ) => v
      case _                 => "parse error"
    } catch { case _: IOException => "error" }
  override val isInstalled: Boolean = version == "3.0.0"

  def apply( code: String ): Either[String, Unit] =
    withTempFile.fromString( code ) { inputFile =>
      runProcess.withExitValue( Seq( executable, "-j0", inputFile.toString ), catchStderr = true ) match {
        case ( 0, _ )   => Right( () )
        case ( _, out ) => Left( out )
      }
    }

  def apply( ctx: Context ): Either[String, Unit] =
    apply( LeanExporter( ctx, includeDirectly = true ) )

  def apply( ctx: Context, p: LKProof ): Either[String, Unit] =
    apply( LeanExporter( ctx, p, includeDirectly = true ) )
}
