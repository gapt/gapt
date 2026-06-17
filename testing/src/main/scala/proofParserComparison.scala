package gapt.testing.proofParserComparison

import java.util.concurrent.ArrayBlockingQueue

import scala.collection.parallel.CollectionConverters._
import scala.concurrent.duration._
import gapt.formats.tptp.TptpProofParser
import scala.concurrent.Await
import scala.concurrent.Future
import scala.concurrent.TimeoutException

val messageEndMarker = "__GAPT_PROOF_PARSING_WORKER_MESSAGE_END__"
@main def worker(name: String): Unit = {
  import scala.concurrent.ExecutionContext.Implicits.global
  Console.err.println(s"[$name] started worker")
  val lines = Iterator
    .continually(scala.io.StdIn.readLine())
    .takeWhile(_ != null)
  for path <- lines do {
    val response =
      try {
        Console.err.println(s"[$name] running parser on $path")
        // note that if TptpProofParser.parse(path) doesn't finish within the
        // timeout it will keep running and using up resources so use this
        // carefully
        Await.result(Future { TptpProofParser.parse(path) }, 5.seconds)
        Console.err.println(s"[$name] finished parsing on $path")
        "ok"
      } catch {
        case _: TimeoutException => {
          Console.err.println(s"[$name] timed out on $path")
          "timeout"
        }
        case e: Throwable => s"fail: $e"
      }

    Console.out.println(response)
    Console.out.println(messageEndMarker)
    Console.out.flush()
    Console.err.flush()
  }

  Console.err.println(s"[$name] stopped worker after receiving EOF")
}

@main def test(): Unit = {
  val buildCommand = Seq(
    "sbt",
    """set testing / Compile / mainClass := Some("gapt.testing.proofParserComparison.worker")""",
    """set testing / assembly / assemblyOutputPath := target.value / "worker.jar"""",
    "testing/assembly"
  )

  def workerCommand(name: String) = Seq(
    "java",
    "-jar",
    "target/worker.jar",
    name
  )

  val oldDir = os.root / "tmp" / "gapt-origin-develop"
  val newDir = os.pwd
  val paths = os.walk(os.pwd / "testing" / "TSTP" / "Solutions").filter(os.isFile)

  // this assumes that the old directory also contains the worker script
  // one way to do this is to the old directory and add a symlink to the worker script
  // so it can be built in the old directory as well
  Console.err.println(s"building worker jar in $oldDir")
  val buildOld = new ProcessBuilder(buildCommand*).directory(oldDir.toIO).start()
  val oldBuildExitCode = buildOld.waitFor()
  if oldBuildExitCode != 0 then
    throw new RuntimeException(s"building old worker failed with exit code $oldBuildExitCode")

  Console.err.println(s"building worker jar in $newDir")
  val buildNew = new ProcessBuilder(buildCommand*).directory(newDir.toIO).start()
  val newBuildExitCode = buildNew.waitFor()
  if newBuildExitCode != 0 then
    throw new RuntimeException(s"building new worker failed with exit code $newBuildExitCode")

  assert(os.exists(oldDir / "target" / "worker.jar"))
  assert(os.exists(newDir / "target" / "worker.jar"))

  val workerPool = WorkerPool(
    size = 3,
    makePair = () =>
      WorkerPair(
        WorkerClient(workerCommand("old"), oldDir),
        WorkerClient(workerCommand("new"), newDir)
      )
  )

  val results =
    try {
      paths.par.flatMap { path =>
        Option.when(!solutionsThatTakeLongToParse.contains(path.lastSegments(2))) {
          Console.err.println(s"computing results for $path")
          workerPool.borrow { workerPair =>
            path ->
              CallResult(
                path,
                workerPair.oldWorker.request(path.toString),
                workerPair.newWorker.request(path.toString)
              )
          }
        }
      }.seq.toMap
    } finally {
      workerPool.close()
    }

  val failures = paths.flatMap { path =>
    results.get(path).flatMap { result =>
      val errors = Seq(
        Option.when(result.isMismatch)(
          s"old and new differ: old=${result.oldResult}, new=${result.newResult}"
        ),
        Option.when(result.oldResult == "timeout")("old timed out"),
        Option.when(result.newResult == "timeout")("new timed out"),
        Option.when(result.oldResult != "ok")(s"old failed: ${result.oldResult}"),
        Option.when(result.newResult != "ok")(s"new failed: ${result.newResult}"),
        Option.when(result.isAccountedForMismatch)("mismatch is accounted for"),
        Option.when(result.isMismatch && !result.isAccountedForMismatch)("mismatch is unaccounted for")
      ).flatten

      Option.when(errors.nonEmpty)(path -> errors)
    }
  }

  failures.foreach { (path, errors) =>
    Console.err.println(s"FAILED $path")
    errors.foreach(error => Console.err.println(s"  ${error.split("\n").head}"))
  }

  val skipped = paths.count(path => solutionsThatTakeLongToParse.exists(p => path.toString.endsWith(p)))
  val mismatches = results.values.count(result => result.isMismatch)
  val accountedForMismatches = results.values.count(_.isAccountedForMismatch)
  val unaccountedForMismatches = mismatches - accountedForMismatches
  val oldTimeouts = results.values.count(_.oldResult == "timeout")
  val newTimeouts = results.values.count(_.newResult == "timeout")
  val knownTimeouts = solutionsThatTakeLongToParse.size
  Console.err.println(s"checked ${results.size} proof files")
  Console.err.println(s"skipped $skipped long-running proof files")
  Console.err.println(s"old/new mismatches: $mismatches")
  Console.err.println(s"unaccounted-for mismatches: $unaccountedForMismatches")
  Console.err.println(s"old timeouts: $oldTimeouts")
  Console.err.println(s"new timeouts: $newTimeouts")
  Console.err.println(s"known timeouts that were not tried: $knownTimeouts")
  Console.err.println(s"failures: ${failures.size}")

  if failures.nonEmpty then sys.exit(1)
}

extension (p: os.Path) {
  def lastSegments(n: Int): String = p.segments.drop(p.segments.size - n).mkString("/")
}

final case class CallResult(path: os.Path, oldResult: String, newResult: String) {
  def isMismatch: Boolean = oldResult.split(":").head != newResult.split(":").head
  def isAccountedForMismatch: Boolean = intendedOldFailNewSucceeded.contains(path.lastSegments(2))
    && oldResult.startsWith("fail")
    && newResult.startsWith("ok")
}

final case class WorkerPair(
    oldWorker: WorkerClient,
    newWorker: WorkerClient
) {
  def close(): Unit = {
    oldWorker.close()
    newWorker.close()
  }
}

final class WorkerPool(size: Int, makePair: () => WorkerPair) {
  private val queue = new ArrayBlockingQueue[WorkerPair](size)
  (1 to size).foreach(_ => queue.put(makePair()))

  def borrow[A](f: WorkerPair => A): A = {
    val pair = queue.take()
    try f(pair)
    finally queue.put(pair)
  }

  def close(): Unit = {
    val pairs = (1 to size).map(_ => queue.take())
    pairs.foreach(_.close())
  }
}

final class WorkerClient(command: Seq[String], cwd: os.Path) {
  private val process =
    new ProcessBuilder(command*)
      .redirectError(ProcessBuilder.Redirect.INHERIT)
      .directory(cwd.toIO)
      .start()

  private val in =
    new java.io.BufferedWriter(
      new java.io.OutputStreamWriter(process.getOutputStream)
    )

  private val out =
    new java.io.BufferedReader(
      new java.io.InputStreamReader(process.getInputStream)
    )

  def request(line: String): String = synchronized {
    in.write(line)
    in.newLine()
    in.flush()

    val response = new StringBuilder
    var done = false

    while !done do {
      val line = out.readLine()
      if line == null then
        throw new RuntimeException(s"Worker exited with code ${process.waitFor()}")

      if line == messageEndMarker then done = true
      else {
        if response.nonEmpty then response.append('\n')
        response.append(line)
      }
    }

    response.toString()
  }

  def close(): Unit = {
    in.close()
    process.destroy()
  }
}

val solutionsThatTakeLongToParse = Seq(
  "PUZ075+1.p/metis.tstp",
  "SYN362+1.p/metis.tstp",
  "SYN007+1.014.p/metis.tstp",
  "ALG043+1.p/metis.tstp",
  "PUZ075+1.p/eprover.tstp",
  "ALG022+1.p/eprover.tstp",
  "ALG181+1.p/eprover.tstp",
  "ALG208+1.p/eprover.tstp",
  "ALG209+1.p/eprover.tstp",
  "ALG182+1.p/eprover.tstp",
  "ALG168+1.p/eprover.tstp",
  "ALG031+1.p/eprover.tstp",
  "ALG021+1.p/eprover.tstp",
  "ALG186+1.p/eprover.tstp",
  "ALG180+1.p/eprover.tstp",
  "ALG183+1.p/eprover.tstp",
  "ALG184+1.p/eprover.tstp",
  "ALG033+1.p/eprover.tstp",
  "ALG185+1.p/eprover.tstp",
  "ALG187+1.p/eprover.tstp",
  "ALG121+1.p/eprover.tstp",
  "ALG082+1.p/eprover.tstp",
  "ALG083+1.p/eprover.tstp",
  "ALG032+1.p/eprover.tstp",
  "ALG081+1.p/eprover.tstp",
  "ALG095+1.p/eprover.tstp",
  "ALG094+1.p/eprover.tstp",
  "ALG080+1.p/eprover.tstp",
  "ALG043+1.p/eprover.tstp",
  "ALG123+1.p/eprover.tstp",
  "ALG084+1.p/eprover.tstp",
  "ALG090+1.p/eprover.tstp",
  "ALG091+1.p/eprover.tstp",
  "ALG085+1.p/eprover.tstp",
  "ALG118+1.p/eprover.tstp",
  "ALG078+1.p/eprover.tstp",
  "ALG044+1.p/eprover.tstp",
  "ALG093+1.p/eprover.tstp",
  "ALG087+1.p/eprover.tstp",
  "ALG086+1.p/eprover.tstp",
  "ALG092+1.p/eprover.tstp",
  "ALG079+1.p/eprover.tstp",
  "ALG075+1.p/eprover.tstp",
  "ALG115+1.p/eprover.tstp",
  "ALG117+1.p/eprover.tstp",
  "ALG063+1.p/eprover.tstp",
  "ALG077+1.p/eprover.tstp",
  "ALG088+1.p/eprover.tstp",
  "ALG089+1.p/eprover.tstp",
  "ALG076+1.p/eprover.tstp",
  "ALG062+1.p/eprover.tstp",
  "ALG058+1.p/eprover.tstp",
  "ALG067+1.p/eprover.tstp",
  "ALG188+1.p/eprover.tstp",
  "ALG189+1.p/eprover.tstp",
  "ALG207+1.p/eprover.tstp",
  "ALG206+1.p/eprover.tstp",
  "ALG204+1.p/eprover.tstp",
  "ALG205+1.p/eprover.tstp",
  "CSR024+1.010.p/vampire.tstp",
  "PUZ075+1.p/vampire.tstp",
  "PUZ074+1.p/vampire.tstp",
  "SYO525+1.015.p/vampire.tstp",
  "ALG156+1.p/vampire.tstp",
  "ALG195+1.p/vampire.tstp",
  "ALG022+1.p/vampire.tstp",
  "ALG208+1.p/vampire.tstp",
  "ALG209+1.p/vampire.tstp",
  "ALG157+1.p/vampire.tstp",
  "ALG143+1.p/vampire.tstp",
  "SYO525+1.015.p/vampire.tstp",
  "SYN007+1.014.p/vampire.tstp",
  "ALG155+1.p/vampire.tstp",
  "ALG169+1.p/vampire.tstp",
  "ALG021+1.p/vampire.tstp",
  "ALG197+1.p/vampire.tstp",
  "ALG168+1.p/vampire.tstp",
  "ALG140+1.p/vampire.tstp",
  "ALG154+1.p/vampire.tstp",
  "ALG144+1.p/vampire.tstp",
  "ALG187+1.p/vampire.tstp",
  "ALG187+1.p/vampire.tstp",
  "ALG186+1.p/vampire.tstp",
  "ALG145+1.p/vampire.tstp",
  "ALG151+1.p/vampire.tstp",
  "ALG147+1.p/vampire.tstp",
  "ALG153+1.p/vampire.tstp",
  "ALG033+1.p/vampire.tstp",
  "ALG026+1.p/vampire.tstp",
  "ALG032+1.p/vampire.tstp",
  "ALG152+1.p/vampire.tstp",
  "ALG146+1.p/vampire.tstp",
  "ALG121+1.p/vampire.tstp",
  "ALG055+1.p/vampire.tstp",
  "ALG055+1.p/vampire.tstp",
  "ALG068+1.p/vampire.tstp",
  "ALG108+1.p/vampire.tstp",
  "ALG134+1.p/vampire.tstp",
  "ALG120+1.p/vampire.tstp",
  "ALG122+1.p/vampire.tstp",
  "ALG056+1.p/vampire.tstp",
  "ALG095+1.p/vampire.tstp",
  "ALG094+1.p/vampire.tstp",
  "ALG057+1.p/vampire.tstp",
  "ALG043+1.p/vampire.tstp",
  "ALG123+1.p/vampire.tstp",
  "ALG133+1.p/vampire.tstp",
  "ALG127+1.p/vampire.tstp",
  "ALG053+1.p/vampire.tstp",
  "ALG090+1.p/vampire.tstp",
  "ALG091+1.p/vampire.tstp",
  "ALG126+1.p/vampire.tstp",
  "ALG118+1.p/vampire.tstp",
  "ALG124+1.p/vampire.tstp",
  "ALG050+1.p/vampire.tstp",
  "ALG044+1.p/vampire.tstp",
  "ALG093+1.p/vampire.tstp",
  "ALG092+1.p/vampire.tstp",
  "ALG045+1.p/vampire.tstp",
  "ALG051+1.p/vampire.tstp",
  "ALG131+1.p/vampire.tstp",
  "ALG125+1.p/vampire.tstp",
  "ALG119+1.p/vampire.tstp",
  "ALG100+1.p/vampire.tstp",
  "ALG128+1.p/vampire.tstp",
  "ALG060+1.p/vampire.tstp",
  "ALG049+1.p/vampire.tstp",
  "ALG129+1.p/vampire.tstp",
  "ALG115+1.p/vampire.tstp",
  "ALG101+1.p/vampire.tstp",
  "ALG117+1.p/vampire.tstp",
  "ALG103+1.p/vampire.tstp",
  "ALG063+1.p/vampire.tstp",
  "ALG062+1.p/vampire.tstp",
  "ALG102+1.p/vampire.tstp",
  "ALG106+1.p/vampire.tstp",
  "ALG066+1.p/vampire.tstp",
  "ALG099+1.p/vampire.tstp",
  "ALG067+1.p/vampire.tstp",
  "ALG059+1.p/vampire.tstp",
  "ALG064+1.p/vampire.tstp",
  "ALG064+1.p/vampire.tstp",
  "ALG058+1.p/vampire.tstp",
  "ALG058+1.p/vampire.tstp",
  "ALG163+1.p/vampire.tstp",
  "ALG163+1.p/vampire.tstp",
  "ALG188+1.p/vampire.tstp",
  "ALG188+1.p/vampire.tstp",
  "ALG189+1.p/vampire.tstp",
  "ALG189+1.p/vampire.tstp",
  "ALG162+1.p/vampire.tstp",
  "ALG162+1.p/vampire.tstp",
  "ALG160+1.p/vampire.tstp",
  "ALG148+1.p/vampire.tstp",
  "ALG161+1.p/vampire.tstp",
  "ALG159+1.p/vampire.tstp",
  "ALG207+1.p/vampire.tstp",
  "ALG164+1.p/vampire.tstp",
  "ALG169+1.p/eprover.tstp",
  "ALG048+1.p/vampire.tstp",
  "ALG158+1.p/vampire.tstp",
  "ALG166+1.p/vampire.tstp",
  "ALG167+1.p/vampire.tstp"
)

val intendedOldFailNewSucceeded = Seq(
  "ALG173+1.p/eprover.tstp",
  "ALG172+1.p/eprover.tstp",
  "ALG170+1.p/eprover.tstp",
  "ALG039+1.p/eprover.tstp",
  "ALG171+1.p/eprover.tstp",
  "ALG014+1.p/eprover.tstp",
  "ALG174+1.p/eprover.tstp",
  "ALG016+1.p/eprover.tstp",
  "ALG017+1.p/eprover.tstp",
  "ALG110+1.p/eprover.tstp",
  "ALG111+1.p/eprover.tstp",
  "ALG105+1.p/eprover.tstp",
  "ALG113+1.p/eprover.tstp",
  "ALG113+1.p/eprover.tstp",
  "ALG045+1.p/eprover.tstp",
  "ALG042+1.p/eprover.tstp",
  "ALG020+1.p/eprover.tstp",
  "ALG037+1.p/eprover.tstp",
  "ALG036+1.p/eprover.tstp",
  "ALG114+1.p/eprover.tstp",
  "SWV139+1.p/eprover.tstp",
  "SWV132+1.p/eprover.tstp",
  "SWV131+1.p/eprover.tstp",
  "SWV142+1.p/eprover.tstp",
  "SWV143+1.p/eprover.tstp",
  "SWV141+1.p/eprover.tstp",
  "SWV140+1.p/eprover.tstp",
  "SWV144+1.p/eprover.tstp",
  "CSR016+1.p/eprover.tstp",
  "CSR023+1.p/eprover.tstp",
  "CSR018+1.p/eprover.tstp"
)

val toLookInto = Seq(
  "SWV128+1.p/eprover.tstp",
  "SWV106+1.p/eprover.tstp",
  "SWV121+1.p/eprover.tstp"
)
