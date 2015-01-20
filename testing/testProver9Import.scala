import java.io._
import scala.io.Source

/**********
 * test script for prover9 import, usage example from CLI:
 *
 * scala> :load testing/testProver9Import.scala
 * scala> testProver9Import( "testing/TSTP/prover9/", 60, Some( "results_revXXXX_loadProver9LKProof_60sec.txt" ))
 **********/

/**
 * A wrapper around file, allowing iteration either on direct children or on directory tree
 **/
class MyFile(file: File) {

  def children = new Iterable[File] {
    def iterator = if (file.isDirectory) file.listFiles.iterator else Iterator.empty
  }

  def andTree : Iterable[File] =
    Seq(file) ++ children.flatMap(child => new MyFile(child).andTree)
}

class MyOption[+T >: Nothing]
case object MyNone extends MyOption[Nothing]
case class MyThrowable[+T >: Nothing](exp: Throwable) extends MyOption[T]
case class MySome[+T >:Nothing](value: T) extends MyOption[T]

/**
 * takes a directory name and a timeout (in seconds) as argument,
 * processes all .out-files below the given directory
 **/
object testProver9Import {

  type MyMap = scala.collection.mutable.Map[String,List[Pair[String,Option[Throwable]]]]

  def apply( dir: String, to: Long, fn: Option[String] = None ) {
    println( "Testing prover9-import with timeout " + to + "s:" )
    var n_total = 0
    var n_exp = 0
    var n_none = 0
    var n_OK = 0

    var list_succ = List[String]()
    val map_failure = scala.collection.mutable.Map[String,List[Pair[String,Option[Throwable]]]]()

    val root = new MyFile( new File( dir ) )

    val cur = System.currentTimeMillis

    var out = System.out
    val err = System.err
    System.setOut(new java.io.PrintStream(new java.io.ByteArrayOutputStream()))
    System.setErr(new java.io.PrintStream(new java.io.ByteArrayOutputStream()))

    for ( file <- root.andTree if file.getName.endsWith( ".out" ) ) {
      n_total += 1
      //print( "  " + file.getName() + " " )
      out.println(n_total + " - " +( file.toString) + " - " + ((System.currentTimeMillis - cur) / 1000))

      val suc_import = runWithTimeout( to * 1000 ) {
      loadProver9LKProof( file.getCanonicalPath() )
      }
      suc_import match {
        case MyNone => {
          //println( "[ FAIL ]" )
          addOrUpdate(map_failure, "None", file.getCanonicalPath(), None)
        }
        case MyThrowable(ex) => {
          //println( "[ FAIL " + ex.getClass.getName + " ]")
          val loc = locateGAPTLocation(ex.getStackTrace())
          addOrUpdate(map_failure, loc,file.getCanonicalPath(), Some(ex))
        }
        case _ => {
          n_OK += 1
          //println ("[ OK ]" )
          list_succ = file.getCanonicalPath() :: list_succ
        }
      }
    }

    System.setErr(err)
    System.setOut(out)
    fn match {
      case Some(fn) => {
        out = new PrintStream(new File(fn))
      }
      case _ => ()
    }

    out.println( "\nTotal Stats: " + n_OK + "/" + n_total + " OK" )
    out.println( "Successes:" )
    list_succ.foreach( e => out.println ( "  " + e ) )
    out.println( "Failures:" )
    map_failure.keySet.foreach( e => out.println( "  " + e + " -> " + map_failure(e).size))
    map_failure.keySet.foreach(
      e => {out.println( " Error: " + e + "\n" + "------------- list of affected files ---------------------------"); map_failure(e).foreach(
        e => {out.println( "  " + e._1); (e._2 match {case None => out.println("timeout (" + to + ")"); case Some(ex) => ex.printStackTrace})});
      out.println("\n============= end of list =========================================")})

    out.flush
    out.close
  }

  /**
   * Run f
   *
   * If f terminates within to milliseconds return its result, if it throws an
   * exception or does not terminate within to milliseconds, return None.
   **/
  private def runWithTimeout[T >: Nothing]( to: Long )( f: => T ) : MyOption[T] = {
    var output:MyOption[T] = MyNone

    val r = new Runnable { def run() { try { output = MySome( f ) } catch {
      case ex: Throwable => output = MyThrowable(ex)
    } } }
    val t = new Thread( r )
    t.start()
    t.join( to )
    if ( t.isAlive() ) t.stop()

    output
  }

  private def addOrUpdate(map: MyMap, err: String, value: String, ex: Option[Throwable]) = {
    try {
      val ls = map(err)
      map(err) = (value,ex) :: ls
    } catch {
      case nsee: NoSuchElementException =>  map(err) = List((value,ex))
    }

  }

  private def locateGAPTLocation(elems: Array[StackTraceElement]): String = {
    // we concatenate the stack as an identifier for a specific error (we ignore the ex message)
    // we take first 3 elements as they are normally enough to identify the location in the gapt code
    // nornmally, we should look for patterns and cut the stack trace there in order to avoid
    // different map keys for the same errors but with different depth of nesting
    elems.take(3).foldLeft("")((str,e) => str ++ e.toString ++ "\n")
  }
}
