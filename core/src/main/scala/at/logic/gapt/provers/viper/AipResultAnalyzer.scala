package at.logic.gapt.provers.viper

import scala.io.Source

private class ParseException( message: String ) extends Exception( message );
case class RunData( prover: String, axiomType: String, file: String, status: String, computationTime: Double )
case class Summary( prover: String, summaries: Seq[AxiomSummary] )
case class AxiomSummary(
  axiomType:  String,
  successes:  Int,
  failures:   Int,
  errors:     Int,
  avgTime:    Double,
  medianTime: Double,
  minTime:    Double,
  maxTime:    Double
)

class AipResultAnalyzer( file: String ) {

  val data = parseRunData( Source.fromFile( file ) )

  private def parseRunData( data: Source ): Seq[RunData] =
    for {
      line <- data.getLines().toSeq
      if !isComment( line )
      if !line.trim.isEmpty
    } yield parseDataLine( line )

  private def isComment( line: String ) = line.trim.startsWith( "#" )

  private def parseDataLine( line: String ): RunData = {
    val tokens = line.trim.split( " +" )
    if ( tokens.length != 5 ) {
      println( line )
      throw new ParseException( s"$file: Too few fields on line" )
    } else
      RunData( tokens( 0 ), tokens( 1 ), tokens( 2 ), tokens( 3 ), parseComputationTime( tokens( 4 ) ) )
  }

  private def parseComputationTime( data: String ) =
    try {
      data.toDouble
    } catch {
      case e: NumberFormatException => throw new ParseException( s"$file: Invalid computation time: " + data )
    }

  def summarize(): Seq[Summary] = {
    val provers = data map { _.prover } distinct

    def summarizeProver( prover: String ): Summary = {
      val proverData = data filter { _.prover == prover }
      val axiomTypes = proverData.map( _.axiomType ).distinct

      def summarizeAxiomType( axiomType: String ): AxiomSummary = {
        val axiomData = proverData.filter( _.axiomType == axiomType )
        val computationTimes = axiomData.filter( _.status != "error" ).map( _.computationTime )
        AxiomSummary(
          axiomType,
          axiomData.filter( _.status == "success" ).length,
          axiomData.filter( _.status == "failure" ).length,
          axiomData.filter( _.status == "error" ).length,
          if ( computationTimes.isEmpty ) Double.NaN else computationTimes.sum / computationTimes.length,
          if ( computationTimes.isEmpty ) Double.NaN else Statistics.median( computationTimes ),
          if ( computationTimes.isEmpty ) Double.NaN else computationTimes.min,
          if ( computationTimes.isEmpty ) Double.NaN else computationTimes.max
        )
      }
      Summary( prover, axiomTypes map { summarizeAxiomType( _ ) } )
    }
    provers map { summarizeProver( _ ) }
  }
}

private object Statistics {
  def mean( vs: Seq[Double] ) = vs.sum / vs.length
  def median( vs: Seq[Double] ) = vs.sorted.drop( vs.length / 2 ).head
}

object ara {
  def main( args: Array[String] ): Unit = {
    if ( args.isEmpty ) {
      println( "usage: ara file..." )
      sys exit 1
    }
    try
      args.zip( args.map( new AipResultAnalyzer( _ ).summarize() ) ).foreach {
        case ( file, summaries ) => {
          println( s"$file:" )
          summaries foreach { s: Summary => println( renderSummary( s ) ) }
          println
        }
      }
    catch {
      case e: ParseException => println( e.getMessage )
    }
  }
  private def renderSummary( summary: Summary ): String = {
    def renderAxiomSummary( a: AxiomSummary ): String = {
      """  %s
        |    %d successes
        |    %d failures
        |    %d abnormal terminations
        |    %.2f/%.2f/%.2f/%.2f avg/median/min/max runtime in s """.stripMargin.format(
        a.axiomType,
        a.successes,
        a.failures,
        a.errors,
        a.avgTime,
        a.medianTime,
        a.minTime,
        a.maxTime
      )
    }
    def renderAxiomSummaries( as: Seq[AxiomSummary] ): String =
      as match {
        case Seq()              => ""
        case Seq( a )           => renderAxiomSummary( a )
        case Seq( a, ass @ _* ) => renderAxiomSummary( a ) + "\n" + renderAxiomSummaries( ass )
      }
    "%s\n%s".format( summary.prover, renderAxiomSummaries( summary.summaries ) )
  }
}