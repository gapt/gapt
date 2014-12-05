import java.io.{FileWriter, File}
import at.logic.calculi.lk.base.LKRuleCreationException
import at.logic.cli.GAPScalaInteractiveShellLibrary.loadProver9LKProof
import at.logic.utils.executionModels.timeout._

object runOnProver9Proofs {
  val basePath = "../testing/TSTP/prover9/"
  val logDirPath = "../testing/logs"
  val timeOut = 60

  def getFileList(path: String = "") = getFileListRec(basePath + path) sortBy {
    p => new File(p).length()
  }

  def getFileListRec(path: String): List[String]  = {
    val file = new File(path)
    if (file.isDirectory) {
      val children = file.listFiles
      (children map (_.getPath) flatMap getFileListRec).toList
    }
    else if (file.getName.endsWith(".s.out"))
      List(file.getPath)
    else
      Nil
  }

  def apply(f: (String) => Unit)(path: String = ""): Unit = {
    val files = getFileList(path)

    val logDir = new File(logDirPath)

    if (logDir.exists()) {
      val logs = logDir.listFiles()
      logs.foreach {_.delete()}
      logDir.delete()
    }


    files.foreach {f}
  }

  def testImport(path: String): Unit = {

    val currentDir =  {
      val tmp = new File(path)
      tmp.getParentFile.getParentFile.getName
    }

    val logDir = new File(logDirPath)

    if (!logDir.exists())
      logDir.mkdir()

    println(path)
    try {
      withTimeout(1000 * timeOut)
      {loadProver9LKProof(path)}
    }

    catch {
      case e: LKRuleCreationException =>
        val logFileName = logDirPath + currentDir + ".txt"
        println(logFileName)
        val writer = new FileWriter(logFileName, true)
        writer.append(path+"\n")
        writer.append(e.toString+"\n\n")
        writer.close()

      case _: Throwable =>
    }
  }
  //println("Proof successfully imported.")
}