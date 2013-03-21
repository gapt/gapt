import java.io._
import scala.io.Source

/**********
 * test script for the cut-introduction algorithm on output proofs from prover9,
 * usage example from CLI:
 *
 * scala> :load ../testing/testCutIntro.scala
 * scala> testCutIntro( "../testing/prover9-TSTP/", 60 )
 **********/

object testCutIntro {
  var total = 0
  var error_parser = 0
  var error_term_extraction = 0

  def testRec (str : String, timeout : Int) : Unit = {
    val file = new File(str)
    if (file.isDirectory) {
      val children = file.listFiles
      children.foreach(f => testRec(f.getAbsolutePath, timeout))
    }
    else if (file.getName.endsWith(".out")) {
      total += 1
      println("\nFILE: " + file.getAbsolutePath)
      runWithTimeout(timeout * 1000){ loadProver9LKProof(file.getAbsolutePath) } match {
        case Some(p) => 
          runWithTimeout(timeout * 1000){ 
            val ts = extractTerms(p)
            val tssize = ts.termset.size
            val n_functions = ts.formulaFunction.size
            if(tssize > n_functions) {
              tssize
            }
            else 0
            //cutIntro(p) 
          } match {
            case Some(n) =>
              if(n > 0) {
                println("File: " + file.getAbsolutePath + " has term-set of size " + n)
              }
              //val name = file.getName + ".lk"
              //exportXML(List(p, p_cut), List(name, name+".lk_with_cut"), "../../../testing/resultsCutIntro/"+name)
            case None => error_term_extraction += 1
          }
        case None => error_parser += 1
      }
    }       
  }

  def apply ( str : String, timeout : Int) = {
    testRec(str, timeout)
    println("Total number of proofs: " + total)
    println("Time limit exceeded or exception during parsing: " + error_parser)
    println("Time limit exceeded or exception during terms extraction: " + error_term_extraction)
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

