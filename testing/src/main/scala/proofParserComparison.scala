package gapt.testing.proofParserComparison

import scala.collection.parallel.CollectionConverters._
import scala.concurrent.duration._
import gapt.utils.withTimeout
import gapt.utils.TimeOutException
import gapt.formats.tptp.TptpProofParser

val messageEndMarker = "__GAPT_PROOF_PARSING_WORKER_MESSAGE_END__"
@main def worker(): Unit = {
  Console.err.println("running worker")
  val lines = Iterator
    .continually(scala.io.StdIn.readLine())
    .takeWhile(_ != null)
  for path <- lines do {
    val response =
      try {
        withTimeout(5.seconds) {
          TptpProofParser.parse(path)
        }
        "ok"
      } catch {
        case _: TimeOutException => {
          Console.err.println(s"timed out on $path")
          "timeout"
        }
        case e: Exception => s"fail: $e"
      } finally {
        Console.out.flush()
      }

    Console.out.println(response)
    Console.out.println(messageEndMarker)
  }

  Console.err.println("stopped worker after receiving EOF")
}

@main def test(): Unit = {
  val buildCommand = Seq(
    "sbt",
    """set testing / Compile / mainClass := Some("gapt.testing.proofParserComparison.worker")""",
    """set testing / assembly / assemblyOutputPath := target.value / "worker.jar"""",
    "testing/assembly"
  )

  val workerCommand = Seq(
    "java",
    "-jar",
    "target/worker.jar"
  )

  val oldDir = os.root / "tmp" / "gapt-origin-develop"
  val newDir = os.pwd
  val paths = os.walk(os.pwd / "testing" / "TSTP" / "Solutions").filter(os.isFile)
  val longRunning = Seq(
    "PUZ075+1.p/metis.tstp",
    "SYN362+1.p/metis.tstp",
    "SYN007+1.014.p/metis.tstp",
    "ALG043+1.p/metis.tstp"
  )

  // this assumes that the old directory also contains the worker script
  // one way to do this is to the old directory and add a symlink to the worker script
  // so it can be built in the old directory as well
  println(s"building worker jar in $oldDir")
  val buildOld = new ProcessBuilder(buildCommand*).directory(oldDir.toIO).start()
  val oldBuildExitCode = buildOld.waitFor()
  if oldBuildExitCode != 0 then
    throw new RuntimeException(s"building old worker failed with exit code $oldBuildExitCode")

  println(s"building worker jar in $newDir")
  val buildNew = new ProcessBuilder(buildCommand*).directory(newDir.toIO).start()
  val newBuildExitCode = buildNew.waitFor()
  if newBuildExitCode != 0 then
    throw new RuntimeException(s"building new worker failed with exit code $newBuildExitCode")

  assert(os.exists(oldDir / "target" / "worker.jar"))
  assert(os.exists(newDir / "target" / "worker.jar"))

  val workerPair = WorkerPair(
    WorkerClient(workerCommand, oldDir),
    WorkerClient(workerCommand, newDir)
  )

  val results =
    try {
      paths.par.flatMap { path =>
        Option.when(!longRunning.exists(p => path.toString.endsWith(p))) {
          println(s"computing results for $path")
          workerPair.synchronized {
            path ->
              CallResult(
                workerPair.oldWorker.request(path.toString),
                workerPair.newWorker.request(path.toString)
              )
          }
        }
      }.seq.toMap
    } finally {
      workerPair.close()
    }

  val failures = paths.flatMap { path =>
    results.get(path).flatMap { result =>
      val errors = Seq(
        Option.when(result.oldResult != result.newResult)(
          s"old and new differ: old=${result.oldResult}, new=${result.newResult}"
        ),
        Option.when(result.oldResult == "timeout")("old timed out"),
        Option.when(result.newResult == "timeout")("new timed out"),
        Option.when(result.oldResult != "ok")(s"old failed: ${result.oldResult}"),
        Option.when(result.newResult != "ok")(s"new failed: ${result.newResult}")
      ).flatten

      Option.when(errors.nonEmpty)(path -> errors)
    }
  }

  failures.foreach { (path, errors) =>
    println(s"FAILED $path")
    errors.foreach(error => println(s"  $error"))
  }

  val skipped = paths.count(path => longRunning.exists(p => path.toString.endsWith(p)))
  println(s"checked ${results.size} proof files")
  println(s"skipped $skipped long-running proof files")
  println(s"failures: ${failures.size}")

  if failures.nonEmpty then sys.exit(1)
}

final case class CallResult(oldResult: String, newResult: String)

final case class WorkerPair(
    oldWorker: WorkerClient,
    newWorker: WorkerClient
) {
  def close(): Unit = {
    oldWorker.close()
    newWorker.close()
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
