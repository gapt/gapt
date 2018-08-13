package gapt.examples

import gapt.formats.csv.{ CSVFile, CSVRow }
import gapt.formats.tptp.statistics._
import gapt.utils.time
import java.io._

object CASCEvaluation {
  def apply( prefix: String, print_statistics: Boolean = false ) = {
    val data = CASCData.prepareProblems( prefix )
    val bundle = processFiles( data, print_statistics )
    eval( bundle )
  }

  def saveResult[T <: FileData]( filename: String, bundle: ResultBundle[T] ) = {
    var oos: ObjectOutputStream = null
    try {
      oos = new ObjectOutputStream( new FileOutputStream( filename ) )
      oos.writeObject( bundle )
    } catch {
      case e: Exception =>
        println( s"error writing to $filename: ${e.getMessage()}" )
    } finally {
      if ( oos != null )
        oos.close
    }
  }

  def loadResult[T <: FileData]( filename: String ): Option[ResultBundle[T]] = {
    var ois: ObjectInputStream = null
    try {
      ois = new ObjectInputStream( new FileInputStream( filename ) )
      Some( ois.readObject.asInstanceOf[ResultBundle[T]] )
    } catch {
      case e: Exception =>
        println( s"error reading from $filename: ${e.getMessage()}" )
        None
    } finally {
      ois.close
    }
  }

  def processFiles[T <: FileData]( data: Iterable[T], print_statistics: Boolean = false ) =
    time( TstpStatistics.applyAll( data, print_statistics ) )

  def eval[T <: CASCResult]( bundle: ResultBundle[T] ) = {
    val ( rstatsByProver, rstatsByProblem, rallSolved ) = TstpStatistics.bagResults( bundle.rp_stats )
    val ( sstatsByProver, sstatsByProblem, sallSolved ) = TstpStatistics.bagResults( bundle.tstp_stats )

    println( "=== reconstruction statistics" )
    eval_errors(
      "Total",
      bundle.tstp_stats.size + bundle.tstp_errors.size,
      bundle.tstp_stats.keySet.flatMap( x => Set( bundle.tstp_stats( x ) ) ),
      bundle.rp_stats.keySet.flatMap( x => Set( bundle.rp_stats( x ) ) ),
      TstpStatistics.bagErrors( bundle.tstp_errors ),
      TstpStatistics.bagErrors( bundle.rp_errors ) )

    for ( p <- sstatsByProver.keySet.toList.sorted ) {
      val p_tstp_errors = bundle.tstp_errors.filter( _.file.prover == p )
      val tstp_e_bags = TstpStatistics.bagErrors( p_tstp_errors )
      val rp_e_bags = TstpStatistics.bagErrors( bundle.rp_errors.filter( _.file.prover == p ) )
      eval_errors( p, sstatsByProver( p ).size + p_tstp_errors.size, sstatsByProver( p ), rstatsByProver( p ), tstp_e_bags, rp_e_bags )
    }

    val before_replayed = for ( f <- bundle.rp_stats.keySet.toList ) yield { ( bundle.tstp_stats( f ), bundle.rp_stats( f ) ) }

    println

    println( "=== Tstp DAG vs Replayed Proof Statistics" )
    eval_before_after( before_replayed, depthRatio[T], "depth ratio" )
    eval_before_after( before_replayed, dagRatio[T], "dag ratio  " )

    val provers = bundle.rp_stats.keySet.map( _.prover )
    for ( p <- provers ) {
      val br = before_replayed.filter( _._2.name.prover == p )
      println( s"==           Prover $p " )
      eval_before_after( br, depthRatio[T], "  depth ratio" )
      eval_before_after( br, dagRatio[T], "  dag ratio  " )
    }

  }

  def dagRatio[T <: CASCResult]( pair: ( TstpProofStats[T], RPProofStats[T] ) ) = {
    BigDecimal( pair._2.dagSize ) / BigDecimal( pair._1.dagSize )
  }
  def depthRatio[T <: CASCResult]( pair: ( TstpProofStats[T], RPProofStats[T] ) ) = {
    BigDecimal( pair._2.depth ) / BigDecimal( pair._1.depth )
  }

  def eval_before_after[T <: CASCResult](
    before_replayed: Seq[( TstpProofStats[T], RPProofStats[T] )],
    ratio:           Tuple2[TstpProofStats[T], RPProofStats[T]] => BigDecimal,
    description:     String                                                   = "",
    tex:             Boolean                                                  = true ) = {
    val replay_shrank2 = before_replayed.filter( ratio( _ ) < 0.5 )
    val replay_shrank = before_replayed.filter( ratio( _ ) < 1 )
    val replay_expanded = before_replayed.filter( ratio( _ ) > 1 )
    val replay_same = before_replayed.filter( ratio( _ ) == 1 )
    val replay_expanded2 = before_replayed.filter( ratio( _ ) > 2 )

    //    println( s"pairs       : ${before_replayed.size}" )
    println( s"$description # shrunk x2   : ${replay_shrank2.size}" )
    println( s"$description # shrunk      : ${replay_shrank.size}" )
    println( s"$description # same size   : ${replay_same.size}" )
    println( s"$description # expanded    : ${replay_expanded.size}" )
    println( s"$description # expanded x2 : ${replay_expanded2.size}" )

    if ( tex ) {
      println( s" $description & " +
        List( replay_shrank2, replay_shrank, replay_same, replay_expanded, replay_expanded2 ).map( _.size ).mkString( "", " & ", "\\\\" ) )
    }
    ( replay_shrank, replay_same, replay_expanded )

    //
    //TODO: average sub term depth
    //TODO: average ratio of reused terms
    //TODO:

  }

  def eval_errors[T <: FileData](
    p:           String,
    problems:    Int,
    sstats:      Set[TstpProofStats[T]],
    rpstats:     Set[RPProofStats[T]],
    tstp_e_bags: ErrorBags[T], rp_e_bags: ErrorBags[T],
    tex: Boolean = false ) = {
    val s_count = problems - tstp_e_bags.nf.size
    val s_tstp = sstats.size
    val s_re = tstp_e_bags.resourceErrors().size
    val s_mf = tstp_e_bags.mf.size
    val s_un = tstp_e_bags.internalErrors().size
    val r_rp = rpstats.size
    val r_re = rp_e_bags.resourceErrors().size
    val r_un = rp_e_bags.internalErrors().size
    println( s"$p has ${s_count} tstp solutions" )
    println( s"  constructed proof sketches: ${s_tstp}" )
    println( s"    resource errors         : ${s_re}" )
    println( s"    malformed tstp          : ${s_mf}" )
    println( s"    unsuccessful constr     : ${s_un}" )
    println( s"  reconstructed proofs      : ${r_rp}" )
    println( s"    resource errors         : ${r_re}" )
    println( s"    unsuccessful constr.    : ${r_un}" )

    if ( tex ) {
      println( s" $p & ${s_count} & ${s_tstp} & $s_re & $s_mf & $s_un & $r_rp & $r_re & $r_un \\\\" )
    }

    if ( tstp_e_bags.rg.nonEmpty ) println( "warning: tstp error bag 'gave up' non-empty!" )
    if ( rp_e_bags.mf.nonEmpty ) println( "warning: res proof error bag 'malformed file' non-empty!" )
  }

  def get_depth_to_mindepth_graph[T <: CASCResult]( bundle: ResultBundle[T] ) = {
    val provers = bundle.rp_stats.keySet.map( _.prover ).toList.sorted
    val prover_no = Map[Prover, Int]() ++ ( provers zip ( 1 to provers.size ) )
    val byProblem = TstpStatistics.bagResults( bundle.rp_stats )._2
    val problem_no = Map[Problem, Int]() ++ ( byProblem.keySet.toList zip ( 1 to byProblem.keySet.size ) )
    val minValues: Map[Problem, Int] = byProblem.map( x => ( x._1, x._2.map( y => y.depth ).min ) )

    val data = bundle.rp_stats.toList.map( x =>
      (
        minValues( x._1.problem ), // min depth
        x._2.depth, // current value
        prover_no( x._1.prover ), // prover id
        problem_no( x._1.problem ) ) // problem id
    )
    val rows = data.map( x => CSVRow( List( x._1.toString(), x._2.toString(), x._3.toString(), x._4.toString() ) ) )

    ( data, CSVFile( CSVRow( List( "mindepth", "mydepth", "prover_id", "problem_id" ) ), rows, ", " ) )
  }

}

object CASCData {
  def prepareProblems( prefix: String ) =
    for ( f <- files; p <- provers ) yield {
      CASCResult( s"$prefix/$p/proofs", p, f, ".txt.out" )
    }

  val provers = List(
    "CSE_E---1.0",
    "E---2.2pre",
    "iProver---2.8",
    "Vampire---4.2",
    "Vampire---4.3" )

  /**
   * The problem names of the 2018 CASC competition
   */
  val files = List(
    "AGT013+2", "AGT015+1", "AGT018+1", "AGT019+1", "AGT022+1",
    "AGT022+2", "ALG018+1", "ALG044+1", "ALG092+1", "ALG165+1",
    "ALG210+1", "ALG210+2", "ALG219+1", "BIO002+1", "BOO109+1",
    "CAT032+2", "COM123+1", "COM125+1", "COM126+1", "COM128+1",
    "COM129+1", "COM132+1", "COM133+1", "COM137+1", "COM142+1",
    "COM149+1", "CSR001+2", "CSR015+1", "CSR018+1", "CSR028+3",
    "CSR029+3", "CSR030+6", "CSR031+5", "CSR031+6", "CSR032+3",
    "CSR032+4", "CSR033+6", "CSR035+3", "CSR036+4", "CSR037+3",
    "CSR038+3", "CSR040+3", "CSR041+3", "CSR043+3", "CSR044+5",
    "CSR045+4", "CSR047+3", "CSR047+5", "CSR049+3", "CSR050+6",
    "CSR051+4", "CSR054+3", "CSR055+3", "CSR055+5", "CSR055+6",
    "CSR056+6", "CSR058+3", "CSR059+3", "CSR061+3", "CSR062+3",
    "CSR063+3", "CSR064+3", "CSR067+3", "CSR068+3", "CSR069+3",
    "CSR070+3", "CSR071+6", "CSR072+3", "CSR072+5", "CSR074+3",
    "CSR074+4", "CSR113+15", "CSR113+1", "CSR113+28", "CSR113+29",
    "CSR113+6", "CSR114+12", "CSR114+13", "CSR114+7", "CSR115+32",
    "CSR115+35", "CSR115+40", "CSR115+44", "CSR115+4", "CSR115+53",
    "CSR115+68", "CSR115+6", "CSR115+72", "CSR115+89", "CSR115+92",
    "CSR115+98", "CSR116+16", "CSR116+30", "CSR116+47", "CSR116+7",
    "GEO083+1", "GEO084+1", "GEO089+1", "GEO167+1", "GEO168+1",
    "GEO169+2", "GEO273+1", "GEO274+1", "GEO275+1", "GEO277+1",
    "GEO278+1", "GEO285+1", "GEO289+1", "GEO298+1", "GEO299+1",
    "GEO302+1", "GEO307+1", "GEO309+1", "GEO322+1", "GEO324+1",
    "GEO330+1", "GEO331+1", "GEO338+1", "GEO340+1", "GEO343+1",
    "GEO344+1", "GEO345+1", "GEO440+1", "GEO447+1", "GEO466+1",
    "GEO471+1", "GEO474+1", "GEO477+1", "GEO483+1", "GEO497+1",
    "GEO498+1", "GEO500+1", "GEO504+1", "GEO506+1", "GEO507+1",
    "GEO511+1", "GEO523+1", "GEO524+1", "GEO526+1", "GEO535+1",
    "GEO536+1", "GRA002+1", "GRA002+3", "GRA007+1", "GRA008+2",
    "GRA009+1", "GRA009+2", "GRA011+1", "GRP623+4", "GRP629+3",
    "GRP654+1", "GRP655+1", "GRP655+2", "GRP664+1", "GRP667+1",
    "GRP746+1", "GRP775+1", "GRP777+1", "GRP779+1", "GRP780+1",
    "HAL001+2", "HAL006+1", "HWV041+2", "HWV043+2", "HWV046+2",
    "HWV050+1", "KLE073+1", "KLE084+1", "KLE101+1", "KLE102+1",
    "KLE121+1", "KLE143+2", "KLE170+1.002", "KRS179+1", "KRS180+1",
    "KRS181+1", "KRS186+1", "KRS187+1", "KRS188+1", "KRS190+1",
    "KRS194+1", "KRS195+1", "KRS196+1", "KRS200+1", "KRS201+1",
    "KRS202+1", "KRS203+1", "KRS216+1", "KRS217+1", "KRS233+1",
    "KRS234+1", "KRS235+1", "KRS251+1", "KRS258+1", "KRS259+1",
    "KRS260+1", "KRS261+1", "KRS264+1", "KRS265+1", "KRS266+1",
    "KRS267+1", "LAT258+1", "LAT310+4", "LAT329+4", "LAT332+1",
    "LAT333+3", "LAT348+3", "LAT353+1", "LAT359+2", "LAT360+1",
    "LAT376+4", "LAT379+2", "LCL466+1", "LCL468+1", "LCL474+1",
    "LCL492+1", "LCL494+1", "LCL524+1", "LCL530+1", "LCL541+1",
    "LCL552+1", "LCL553+1", "LCL558+1", "LCL570+1", "LCL572+1",
    "LCL638+1.015", "LCL638+1.020", "LCL642+1.015", "LCL646+1.010",
    "LCL650+1.020", "LCL652+1.015", "LCL656+1.015", "LCL656+1.020",
    "LCL658+1.005", "LCL658+1.010", "LCL658+1.015", "LCL658+1.020",
    "LCL660+1.010", "LCL662+1.015", "LCL664+1.015", "LCL664+1.020",
    "LCL666+1.010", "LCL672+1.010", "LCL672+1.020", "LCL676+1.005",
    "LCL678+1.005", "LCL680+1.005", "LCL682+1.015", "LCL688+1.005",
    "LCL688+1.010", "LCL876+1", "LCL891+1", "LCL892+1", "LCL896+1",
    "LCL898+1", "LCL901+1", "LCL902+1", "MGT005+2", "MGT035+2",
    "MGT047+1", "MGT061+1", "MSC010+1", "NLP260+1", "NLP261+1",
    "NLP262+1", "NUM299+1", "NUM304+1", "NUM320+1", "NUM558+1",
    "NUM847+1", "NUM854+1", "NUM860+1", "NUM862+1", "NUM924+4",
    "NUM924+7", "NUM924+8", "NUM925+4", "NUM925+5", "NUM926+3",
    "NUM926+6", "NUN055+1", "NUN056+1", "NUN057+1", "PRO002+4",
    "PRO003+3", "PRO003+4", "PRO005+1", "PRO005+4", "PRO008+4",
    "PRO016+2", "PUZ076+1", "PUZ078+1", "PUZ128+2", "PUZ133+1",
    "PUZ133+2", "REL016+3", "REL019+1", "REL021+2", "REL022+1",
    "REL028+2", "RNG049+2", "RNG064+2", "SCT102+1", "SCT117+1",
    "SCT121+1", "SCT122+1", "SCT124+1", "SCT128+1", "SCT138+1",
    "SCT139+1", "SCT140+1", "SCT143+1", "SCT144+1", "SCT145+1",
    "SCT147+1", "SCT149+1", "SCT151+1", "SCT154+1", "SCT155+1",
    "SCT158+1", "SCT159+1", "SCT160+1", "SCT162+1", "SCT163+1",
    "SCT169+3", "SCT170+3", "SET016+1", "SET017+1", "SET020+1",
    "SET061+1", "SET098+1", "SET105+1", "SET143+4", "SET155+4",
    "SET171+3", "SET634+3", "SET651+3", "SET722+4", "SET730+4",
    "SET744+4", "SET749+4", "SET750+4", "SEU019+1", "SEU164+1",
    "SEU170+2", "SEU174+2", "SEU187+2", "SEU252+2", "SEU253+1",
    "SEU266+1", "SEU291+1", "SEU325+2", "SEU334+1", "SEU382+1",
    "SEU383+2", "SEU386+1", "SEU418+3", "SWB004+1", "SWB009+1",
    "SWB012+1", "SWB012+3", "SWB014+3", "SWB016+1", "SWB017+1",
    "SWB022+1", "SWB023+1", "SWB027+1", "SWB029+3", "SWB039+1",
    "SWB040+1", "SWB044+1", "SWB045+1", "SWB047+1", "SWB050+1",
    "SWB051+1", "SWB056+1", "SWB057+1", "SWB063+1", "SWB064+1",
    "SWB065+1", "SWB071+1", "SWB073+1", "SWB075+1", "SWB077+1",
    "SWB080+1", "SWB082+1", "SWB083+1", "SWB087+1", "SWB088+1",
    "SWB091+1", "SWB094+1", "SWB097+1", "SWB098+1", "SWB104+1",
    "SWB106+1", "SWB107+1", "SWC043+1", "SWC125+1", "SWV014+1",
    "SWV029+1", "SWV038+1", "SWV089+1", "SWV109+1", "SWV153+1",
    "SWV167+1", "SWV198+1", "SWV199+1", "SWV202+1", "SWV204+1",
    "SWV235+1", "SWV378+1", "SWV393+1", "SWV397+1", "SWV401+1",
    "SWV452+1", "SWV455+1", "SWV461+1", "SWV465+1", "SWV466+1",
    "SWV468+1", "SWV469+1", "SWV475+1", "SWV476+1", "SWV480+1",
    "SWV481+1", "SWV486+1", "SWV486+3", "SWV487+1", "SWV487+3",
    "SWW095+1", "SWW096+1", "SWW098+1", "SWW100+1", "SWW189+1",
    "SWW228+1", "SWW252+1", "SWW256+1", "SWW264+1", "SWW268+1",
    "SWW292+1", "SWW294+1", "SWW295+1", "SWW296+1", "SWW297+1",
    "SWW301+1", "SWW303+1", "SWW304+1", "SWW306+1", "SWW308+1",
    "SWW310+1", "SWW311+1", "SWW313+1", "SWW314+1", "SWW319+1",
    "SWW321+1", "SWW322+1", "SWW326+1", "SWW328+1", "SWW329+1",
    "SWW333+1", "SWW336+1", "SWW337+1", "SWW339+1", "SWW346+1",
    "SWW347+1", "SWW352+1", "SWW355+1", "SWW356+1", "SWW357+1",
    "SWW358+1", "SWW363+1", "SWW364+1", "SWW368+1", "SWW374+1",
    "SWW375+1", "SWW376+1", "SWW377+1", "SWW379+1", "SWW380+1",
    "SWW384+1", "SWW386+1", "SWW391+1", "SWW394+1", "SWW395+1",
    "SWW470+3", "SWW470+6", "SWW473+5", "SWW473+7", "SWW474+5",
    "SWW474+6", "SYN007+1.014", "SYN076+1", "SYN353+1", "SYN986+1.004",
    "SYO525+1.015", "SYO525+1.018", "SYO525+1.021", "SYO604+1",
    "SYO606+1", "TOP041+3" )

}
