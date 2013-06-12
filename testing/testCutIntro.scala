import java.io._
import scala.io.Source
import scala.collection.immutable.HashMap

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
  // Hashmap containing proofs with non-trivial termsets
  var termsets = HashMap[String, FlatTermSet]()

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
              termsets += (file.getAbsolutePath -> ts)
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
    val file = new File("../../../testing/resultsCutIntro/data.csv")
    val summary = new File("../../../testing/resultsCutIntro/summary.txt")
    file.createNewFile()
    summary.createNewFile()
    val fw = new FileWriter(file.getAbsoluteFile)
    val bw = new BufferedWriter(fw)
    val fw_s = new FileWriter(summary.getAbsoluteFile)
    val bw_s = new BufferedWriter(fw_s)

    var instance_per_formula = 0
    var ts_size = 0
    val data = termsets.foldLeft("") {
      case (acc, (k, v)) =>
        val tssize = v.termset.size
        val n_functions = v.formulaFunction.size
        instance_per_formula += tssize/n_functions
        ts_size += tssize
        k + " , " + n_functions + " , " + tssize + "\n" + acc
    }

    val avg_inst_per_form = instance_per_formula/termsets.size
    val avg_ts_size = ts_size/termsets.size

    bw.write(data)
    bw.close()

    bw_s.write("Total number of proofs: " + total + "\n")
    bw_s.write("Total number of proofs with non-trivial termsets: " + termsets.size + "\n")
    bw_s.write("Time limit exceeded or exception during parsing: " + error_parser + "\n")
    bw_s.write("Time limit exceeded or exception during terms extraction: " + error_term_extraction + "\n")
    bw_s.write("Average instances per quantified formula: " + avg_inst_per_form + "\n")
    bw_s.write("Average termset size: " + avg_ts_size + "\n")
    bw_s.close()
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

