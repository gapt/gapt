import java.io._
import scala.io.Source

/**********
 * test script for the cut-introduction algorithm on output proofs from prover9,
 * usage example from CLI:
 *
 * scala> :load ../testing/testCutIntro.scala
 * scala> testCutIntro( "../testing/prover9-TSTP/", 5 )
 **********/

object testCutIntro {
  var total = 0
  var not_parsed = 0
  var not_compressable = 0
  var invalid_rules = 0
  var dont_know = 0
  var time_limit_parser = 0
  var time_limit_cutIntro = 0

  def testRec (str : String, timeout : Int) : Unit = {
    val file = new File(str)
    if (file.isDirectory) {
      val children = file.listFiles
      children.foreach(f => testRec(f.getAbsolutePath, timeout))
    }
    else if (file.getName.endsWith(".out")) {
      try {
        total += 1
        // One minute for each
        runWithTimeout(timeout * 1000){ loadProver9LKProof(file.getAbsolutePath) } match {
            case Some(p) => 
              runWithTimeout(timeout * 1000){ cutIntro(p) } match {
                case Some(p_cut) =>
                  val name = file.getName + ".lk"
                  exportXML(List(p, p_cut), List(name, name+".lk_with_cut"), "../../../testing/resultsCutIntro/"+name)
                case None => time_limit_cutIntro += 1
              }
            case None => time_limit_parser += 1
          }
      }
      catch {
        case pe: at.logic.provers.prover9.Prover9Exception => not_parsed += 1
        case cie: at.logic.algorithms.cutIntroduction.CutIntroException => not_compressable += 1
        case tee: at.logic.algorithms.cutIntroduction.TermsExtractionException => invalid_rules += 1
        case _ => dont_know += 1
      }
    }       
  }

  def apply ( str : String, timeout : Int ) = {
    testRec(str, timeout)
    println("Total number of proofs: " + total)
    println("Number of proofs that were not parsed: " + not_parsed)
    println("Time limit exceeded during parsing: " + time_limit_parser)
    println("Number of proofs that were parsed but not compressed: " + not_compressable)
    println("Time limit exceeded during cut-introduction: " + time_limit_cutIntro)
    println("Don't know what happened (maybe memory limit exceeded?): " + dont_know)
  }

  /**
   * Run f
   *
   * If f terminates within to milliseconds return its result, if it throws an
   * exception or does not terminate within to milliseconds, return None.
   **/
  private def runWithTimeout[T >: Nothing]( to: Long )( f: => T ) : Option[T] = {
    var output:Option[T] = None

    val r = new Runnable { def run() { output = Some( f ) } }
    val t = new Thread( r )
    t.start()
    t.join( to )
    if ( t.isAlive() ) t.stop()

    output
  }
}

