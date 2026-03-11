package gapt.testing

import gapt.expr.{Expr, VarOrConst, App, Abs}
import gapt.expr.subst.{Substitution}
import gapt.logic.hol.ClauseSetPredicateEliminationProblem
import gapt.logic.hol.{scan, wscan}
import gapt.logic.hol.scan.{Derivation, _}
import gapt.utils.{withTimeout}
import scala.concurrent.duration.{Duration, given}
import java.util.concurrent.TimeUnit

def inputSize(clauseSet: ClauseSetPredicateEliminationProblem): Int =
  clauseSet.firstOrderClauses.toSeq.map(c => c.elements.map(numberOfSymbols).sum).sum

def numberOfSymbols(expr: Expr): Int = expr match {
  case _: VarOrConst => 1
  case App(f, args)  => numberOfSymbols(f) + numberOfSymbols(args)
  case Abs(_, inner) => numberOfSymbols(inner)
}

case class ExampleTestResult(
    example: ClauseSetPredicateEliminationProblem,
    derivation: Option[Derivation],
    witness: Option[Substitution],
    startTime: Long,
    scanEndTime: Long,
    wscanEndTime: Long
):
  def exampleSize: Int = inputSize(example)
  def derivationLength: Option[Int] = derivation.map(_.derivationSteps.length)
  def witnessSize: Option[Int] = witness.map(_.map.values.toSeq.map(numberOfSymbols).sum)
  def scanDuration: Duration = Duration.fromNanos(scanEndTime - startTime)
  def witnessDuration: Duration = Duration.fromNanos(wscanEndTime - scanEndTime)
  def totalDuration: Duration = scanDuration + witnessDuration
  def scanDurationPercentage = (scanDuration / totalDuration) * 100.0
  def witnessDurationPercentage = (witnessDuration / totalDuration) * 100.0
  def statisticsString: String = f"""
  |example           = ${example}
  |derivation found  = ${derivation.isDefined}
  |derivation length = ${derivationLength.getOrElse("n/a")}
  |witness found     = ${witness.isDefined}
  |witness size      = ${witnessSize.getOrElse("n/a")}
  |total duration    = ${totalDuration.toUnit(TimeUnit.MILLISECONDS)}%.3f ms
  |scan duration     = ${scanDuration.toUnit(TimeUnit.MILLISECONDS)}%.3f ms ($scanDurationPercentage%.2f%%)
  |witness duration  = ${witness.map(_ => f"${witnessDuration.toUnit(TimeUnit.MILLISECONDS)}%.3f ms").getOrElse("n/a")} ($witnessDurationPercentage%.2f%%)
  """.stripMargin.strip

def runWscanTestExample(example: ClauseSetPredicateEliminationProblem, timeout: Duration): ExampleTestResult = {
  import java.lang.System.nanoTime
  println(s"Testing example ${example}")

  val startTime = nanoTime()
  val derivation =
    try
      withTimeout(timeout) {
        scan(example, derivationLimit = Some(70), attemptLimit = Some(10), allowResolutionOnBaseLiterals = true)
      }
    catch
      case e: gapt.utils.TimeOutException => None

  val scanTime = nanoTime()
  val witness = derivation.flatMap(wscan.witness(_, witnessLimit = Some(10)))
  val wscanTime = nanoTime()

  val result = ExampleTestResult(example, derivation, witness, startTime, scanTime, wscanTime)
  println(result.statisticsString)
  println()
  result
}

def median(xs: Iterable[Long]): Long =
  val sorted = xs.toSeq.sorted
  val lowerIndex = Math.floorDivExact(xs.size, 2)
  val upperIndex = Math.ceilDivExact(xs.size, 2)
  (sorted(lowerIndex) + sorted(upperIndex)) / 2

def medianDouble(xs: Iterable[Double]): Double =
  val sorted = xs.toSeq.sorted
  val lowerIndex = Math.floorDivExact(xs.size, 2)
  val upperIndex = Math.ceilDivExact(xs.size, 2)
  (sorted(lowerIndex) + sorted(upperIndex)) / 2

def minMaxMedAvg[T](xs: Iterable[T])(by: T => Long): (Long, Long, Long, Double) = {
  val min = by(xs.minBy(by))
  val max = by(xs.maxBy(by))
  val med = median(xs.map(by))
  val avg = xs.map(by).sum.toDouble / xs.size
  (min, max, med, avg)
}

def minMaxMedAvgDouble[T](xs: Iterable[T])(by: T => Double): (Double, Double, Double, Double) = {
  val min = by(xs.minBy(by))
  val max = by(xs.maxBy(by))
  val med = medianDouble(xs.map(by))
  val avg = xs.map(by).sum.toDouble / xs.size
  (min, max, med, avg)
}

case class TestRunResult(results: Seq[ExampleTestResult]):
  val resultsWithDerivations = results.filter(_.derivation.isDefined)
  val resultsWithWitnesses = resultsWithDerivations.filter(_.witness.isDefined)
  val foundDerivations = resultsWithDerivations.size
  val foundWitnesses = resultsWithWitnesses.size
  val derivationsSuccessPercentage = (foundDerivations.toDouble / results.size) * 100.0
  val witnessSuccessPercentage = (foundWitnesses.toDouble / foundDerivations) * 100.0
  val (
    minExampleSize,
    maxExampleSize,
    medExampleSize,
    avgExampleSize
  ) = minMaxMedAvg(results)(_.exampleSize)
  val (
    minSuccessfulScanDuration,
    maxSuccessfulScanDuration,
    medSuccessfulScanDuration,
    avgSuccessfulScanDuration
  ) = minMaxMedAvgDouble(resultsWithDerivations)(_.scanDuration.toUnit(TimeUnit.MILLISECONDS))
  val (
    minSuccessfulWitnessDuration,
    maxSuccessfulWitnessDuration,
    medSuccessfulWitnessDuration,
    avgSuccessfulWitnessDuration
  ) = minMaxMedAvgDouble(resultsWithWitnesses)(_.witnessDuration.toUnit(TimeUnit.MILLISECONDS))
  val (
    minWitnessSize,
    maxWitnessSize,
    medWitnessSize,
    avgWitnessSize
  ) = minMaxMedAvg(resultsWithWitnesses)(_.witnessSize.get)
  val failedExamples = results.filter(_.derivation.isEmpty)

  def statisticsString = f"""
  |Tested ${results.size} examples
  |For ${foundDerivations}/${results.size} a derivation could be found ($derivationsSuccessPercentage%.2f%%)
  |For ${foundWitnesses}/${foundDerivations} a witness could be found ($witnessSuccessPercentage%.2f%%)
  |
  |aggregate statistics:
  |
  |example size:
  |min: $minExampleSize
  |max: $maxExampleSize
  |med: $medExampleSize
  |avg: $avgExampleSize%.2f
  |
  |successful scan duration:
  |min: $minSuccessfulScanDuration%.3f ms
  |max: $maxSuccessfulScanDuration%.3f ms
  |med: $medSuccessfulScanDuration%.3f ms
  |avg: $avgSuccessfulScanDuration%.3f ms
  |
  |witness duration:
  |min: $minSuccessfulWitnessDuration%.3f ms
  |max: $maxSuccessfulWitnessDuration%.3f ms
  |med: $medSuccessfulWitnessDuration%.3f ms
  |avg: $avgSuccessfulWitnessDuration%.3f ms
  |
  |witness size:
  |min: $minWitnessSize
  |max: $maxWitnessSize
  |med: $medWitnessSize
  |avg: $avgWitnessSize%.2f
  |
  |${failedExamples.size}/${results.size} failed examples:
  |${failedExamples.map(_.statisticsString).mkString("\n\n")}
  """.stripMargin.strip

def runWscanTest(examples: Seq[ClauseSetPredicateEliminationProblem], timeoutPerExample: Duration): TestRunResult = {
  val runResult = TestRunResult(examples.map(e => runWscanTestExample(e, timeoutPerExample)))
  println(runResult.statisticsString)
  println("Finished run")
  runResult
}

@main
def runWscanBenchmark() = {
  import gapt.examples.predicateEliminationProblems._
  val examples: Vector[ClauseSetPredicateEliminationProblem] = Vector(
    exampleWithQuantifiedVariableNotOccurring,
    exampleWithoutQuantifiedVariables,
    exampleThatCanBeSolvedByPolarityRuleImmediately,
    negationOfLeibnizEquality.toClauseSet,
    exampleThatUsesResolutionOnLiteralsThatAreNotQuantifiedVariables,
    exampleWithTwoClauses,
    exampleWithThreeClauses,
    single2PartDisjunction,
    single3PartDisjunction,
    exampleWithTwoVariables,
    exampleRequiringTautologyDeletion,
    exampleRequiringSubsumption,
    exampleWithSymmetryRequiringSubsumption,
    unsatisfiableExampleThatRequiresFactoring,
    witnessBlowup,
    twoStepRedundancy,
    subsumptionByXLiteral,
    badExample,
    booleanUnification.toClauseSet,
    onlyOneSidedClauses,
    graphReachability(3, 1, 2, 1 -> 2),
    modalCorrespondence.negationOfModalAxiom.toClauseSet,
    modalCorrespondence.negationOfSecondOrderTranslationOfTAxiom,
    modalCorrespondence.negationOfSecondOrderTranslationOf4Axiom,
    wernhardExample06Implicative,
    wernhardExample06Conjunctive,
    wernhardExample06WithoutFirstOrderAssumption,
    soqeBookExample5_4,
    soqeBookExample5_7,
    soqeBookExample6_2_16,
    soqeBookExample6_2_17,
    soqeBookExample6_3,
    soqeBookExample6_4,
    soqeBookExample6_5,
    soqeBookExample6_6,
    soqeBookExample6_23,
    gabbayOhlbachIntroductionExample_1,
    gabbayOhlbachIntroductionExample_2,
    gabbayOhlbachIntroductionExample_3,
    gabbayOhlbachSymmetryExample,
    gabbayOhlbachSection3Example,
    eberhardHetzlWellerExample_4,
    kloibhoferHetzlExample_42
  )
  import java.util.Locale
  Locale.setDefault(Locale.US)
  val timeout = 10.seconds
  for i <- 0 until 2 do
    println(s"Running warmup run $i")
    runWscanTest(examples, timeout)

  println(s"Running test run")
  runWscanTest(examples, timeout)

  println("Finished test")
}
