package at.logic.gapt.provers.viper.aip.cli

import ammonite.ops.FilePath
import at.logic.gapt.formats.tip.{ TipProblem, TipSmtParser }
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.provers.viper.aip.axioms.{ AxiomFactory, IndependentInductionAxioms, SequentialInductionAxioms, UserDefinedInductionAxioms }
import at.logic.gapt.provers.viper.aip.provers._
import at.logic.gapt.provers.viper.aip.{ ProverOptions, _ }

case class AipOptions(
  printSummary: Boolean = false,
  printWitness: Boolean = false,
  printHelp:    Boolean = false,
  witness:      String  = "existential",
  prover:       String  = "escargot",
  axioms:       String  = "sequential",
  infile:       String  = null
)

trait Witness {
  def isPositive: Boolean
}

object aip {

  implicit def bool2Witness( b: Boolean ): Witness = new Witness {
    override def isPositive: Boolean = b

    override def toString(): String = if ( isPositive ) b.toString else "There is no proof"
  }

  implicit def opt2Witness[T]( opt: Option[T] ): Witness = new Witness {
    override def isPositive: Boolean = opt.isDefined

    override def toString(): String = if ( isPositive ) opt.get.toString else "There is no proof"
  }

  case class ValidationException( message: String ) extends Exception( message )

  type AipInvokation[P, W] = ( AnalyticInductionProver, P ) => W

  val axioms = Map[String, AxiomFactory](
    "sequential" -> ( SequentialInductionAxioms().forAllVariables forLabel "goal" ),
    "independent" -> ( IndependentInductionAxioms().forAllVariables forLabel "goal" )
  )

  val provers = Map[String, ResolutionProver](
    "prover9" -> prover9,
    "eprover" -> eprover,
    "escargot" -> escargot,
    "spass" -> spass,
    "vampire" -> vampire
  )

  val witnessAipInvokers = Map[String, AipInvokation[TipProblem, Witness]](
    "existential" -> ( ( aip, p ) => {
      val ( sequent, ctx ) = tipProblemToSequent( p )
      aip.isValid( sequent )( ctx )
    } ),
    "lkproof" -> ( ( aip, p ) => {
      val ( sequent, ctx ) = tipProblemToSequent( p )
      aip.lkProof( sequent )( ctx )
    } ),
    "expansionproof" -> ( ( aip, p ) => {
      val ( sequent, ctx ) = tipProblemToSequent( p )
      aip.expansionProof( sequent )( ctx )
    } ),
    "resolutionproof" -> ( ( aip, p ) => {
      val ( sequent, ctx ) = tipProblemToSequent( p )
      aip.resolutionProof( sequent )( ctx )
    } ),
    "indproof" -> ( ( aip, p ) => {
      aip.proveTipProblem( p )
    } )
  )

  val cmdOptRegex = """--([a-zA-Z0-9-]+)(?:=(.*))?""".r

  def main( args: Array[String] ): Unit = {
    try {
      val options = parseArguments( args.toList )
      if ( options.printHelp ) {
        println( helpMessage )
        System exit 0
      }
      if ( options.infile == null ) {
        throw new ValidationException( usage )
      }
      try {
        val aip = new AnalyticInductionProver( compileProverOptions( options ) )
        val problem = TipSmtParser fixupAndParse FilePath( options.infile )
        val ( witness, t ) = time {
          witnessAipInvokers.get( options.witness ).get( aip, problem )
        }
        val status = if ( witness.isPositive ) "success" else "failure"
        if ( options.printSummary )
          println( summary( options, status, t ) )
        if ( options.printWitness )
          println( witness )
      } catch {
        case e: Exception => {
          val errorMessage = summary( options, "error", -1 )
          System.out.println( errorMessage )
          System.err.print( errorMessage + " : " )
          e.printStackTrace( System.err )
        }
      }
    } catch {
      case ValidationException( message ) => println( message )
    }
  }

  private def summary( options: AipOptions, status: String, time: Long ) = {
    val t =
      if ( time >= 0 )
        "%.2f".format( nanoSeconds2Seconds( time ) )
      else
        "-1"
    "%s %s %s %s %s".format( options.prover, options.axioms, options.infile, status, t )
  }

  private def nanoSeconds2Seconds( ns: Long ): Double = ns.toDouble / 1000000000

  private def time[R]( block: => R ): ( R, Long ) = {
    val t0 = System.nanoTime
    val r = block
    val t1 = System.nanoTime
    ( r, t1 - t0 )
  }

  private def usage: String = "usage: aip [OPTIONS] FILE"

  def parseArguments( args: List[String] ): AipOptions = parseArguments( Map(), args )

  def parseArguments( options: Map[String, String], args: List[String] ): AipOptions = {
    args match {
      case cmdOptRegex( k, v ) :: remainder => parseArguments( options + ( k -> v ), remainder )
      case infile :: Nil                    => parseOptions( options, infile )
      case Nil                              => parseOptions( options, null )
      case _                                => throw new ValidationException( "Illegal command line arguments" )
    }
  }

  private def parseOptions( options: Map[String, String], infile: String ) = {
    options.foldRight( AipOptions( infile = infile ) )( ( opts_, opts ) => parseAndApply( opts_._1, opts_._2, opts ) )
  }

  private def parseAndApply( option: String, value: String, options: AipOptions ): AipOptions =
    option match {
      case "prover" =>
        provers.get( value ) match {
          case None => throw new ValidationException( invalidArgument( option, value ) )
          case _    => options.copy( prover = value )
        }
      case "witness" =>
        witnessAipInvokers.get( value ) match {
          case None => throw new ValidationException( invalidArgument( option, value ) )
          case _    => options.copy( witness = value )
        }
      case "axioms" => options.copy( axioms = value )
      case "print-summary" =>
        if ( value == null )
          options.copy( printSummary = true )
        else
          throw new ValidationException( noArgumentAllowed( option ) )
      case "print-witness" =>
        if ( value == null )
          options.copy( printWitness = true )
        else
          throw new ValidationException( noArgumentAllowed( option ) )
      case "help" =>
        if ( value == null )
          options.copy( printHelp = true )
        else
          throw new ValidationException( noArgumentAllowed( option ) )
      case _ => throw new ValidationException( badOption( option ) )
    }

  private def invalidArgument( option: String, value: String ): String =
    s"Invalid argument `$value' to option '--$option'"

  private def noArgumentAllowed( option: String ): String =
    s"Option '--$option' does not allow an argument"

  private def badOption( option: String ): String =
    s"Unsupported option '--$option'"

  private def helpMessage: String =
    usage + "\n" +
      """Solve the TIP problem specified by FILE by using analytic induction on the goal.
        |
        |  --help             outputs this help text.
        |  --prover           use the specified prover for proof search, possible values for
        |                       this option are: 'escargot', 'prover9', 'vampire', 'spass', 'eprover'.
        |  --axioms           use the specified type of induction axioms, possible values
        |                       are: 'independent', 'sequential' or user defined axioms of the form
        |                       <axiom_1>; <axiom_2>; ... <axiom_n>.
        |  --witness          search for the specified type of proof, legal values are:
        |                       'existential', 'lkproof', 'expansionproof', 'resolutionproof'. If the value
        |                       existential is provided for this option, the prover will only check
        |                       the validity of the given problem without providing a proof.
        |  --print-summary    print a one-liner summarizing the results of the run.
        |  --print-proof      print the proof if one was found.
      """.stripMargin

  private def compileProverOptions( options: AipOptions ): ProverOptions = {
    val inductionType = axioms.get( options.axioms ) match {
      case Some( it ) => it
      case _          => new UserDefinedInductionAxioms( options.axioms.split( ";" )toList )
    }
    ProverOptions( provers.get( options.prover ).get, inductionType )
  }
}
