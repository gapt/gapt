import java.io.{FileWriter, File}
import at.logic.calculi.lk.base.LKRuleCreationException
import at.logic.cli.GAPScalaInteractiveShellLibrary.loadProver9LKProof


object runOnProver9Proofs {
  val basePath = "../testing/TSTP/prover9/"

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

    val logDir = new File("logs")

    if (logDir.exists()) {
      val logs = logDir.listFiles()
      logs.foreach {_.delete()}
      logDir.delete()
    }


    files.foreach {f}
  }

  def testImport(path: String): Unit = {

    val dir =  {
      val tmp = new File(path)
      tmp.getParentFile.getParentFile.getName
    }

    val logDir = new File("logs")

    if (!logDir.exists())
      logDir.mkdir()

    try {
      loadProver9LKProof(path)
    }

    catch {
      case e: LKRuleCreationException =>
        val logFileName = "./logs/" + dir + ".txt"
        println(logFileName)
        val writer = new FileWriter(logFileName, true)
        writer.append(path+"\n")
        writer.append(e.toString+"\n\n")
        writer.close()

      case _ =>
    }
  }
  //println("Proof successfully imported.")
}