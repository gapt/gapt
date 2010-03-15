package at.logic.prooftool

import scala.util.parsing.combinator._
import at.logic.calculi.lk.base._
import java.awt.{Graphics, Font}
import java.awt.geom.Rectangle2D
import at.logic.prooftool.formuladrawing.FontFactory

package formuladrawing {
import util.parsing.combinator.Parsers
import util.parsing.combinator.RegexParsers
import java.awt._
import geom.Rectangle2D
import image.BufferedImage
import scala.List
import util.parsing.input.{CharSequenceReader, Reader}
import swing.{Alignment, Label,Component}
import javax.swing.{Icon, JLabel}
import at.logic.utils.ds.graphs.Graph

class FontFactory(val g:Graphics) {
  val defaultFont = g.getFont

  def getFont(changed_size : Int) = {
    if (changed_size == 0) {
      defaultFont
    } else {
      var size : Float = defaultFont.getSize2D
      size -= Math.abs(changed_size*2)
      if (size<5.0) size = 5.0f

      defaultFont.deriveFont(size)
    }
  }

  /*
  def maxHeight = {
    defaultFont.getMaxCharBounds(g.asInstanceOf[Graphics2D].getFontRenderContext).getHeight.toInt
  }*/

  def maxHeight :Int = maxHeight(0)

  def maxHeight(n:Int) : Int = {
    getFont(n).getMaxCharBounds(g.asInstanceOf[Graphics2D].getFontRenderContext).getHeight.toInt
  }

  def distanceFromBottomLine(n:Int) = {
    if (n>=0) {
      ((0 to n) map (maxHeight(_))).foldLeft (0) (_+_)
    } else /* (n<0) */ {
      /* the asymmmetry stems from the measurement from the bottom line of the 0 height text*/
      - (((1 to -n) map (maxHeight(_))).foldLeft (0) (_+_))
    }
  }
}

class JavaFormulaLabel extends JLabel {
  override def paint(g:Graphics) = {
    val r : Rectangle = g getClipBounds()
    g.fillRect(0,0,r.height,r.width)
    ()
  }
  

}

/*
class TreeLabel[V](val proof : Graph[V]) extends Component {
  
}

class NAryInference[V](val proof : Graph[V]) extends TreeLabel[V](proof) {

}

class LeafInference[V](val formula : V) extends TreeLabel[V] {
  val label = new FormulaLabel()
  label.text = formula.toString

  override def paint(g:Graphics) = {
    val r = formula.
    g.drawRect()
    ()
  }
}
*/

class FormulaLabel  extends Label {
  var parsedString : List[(Int,String)] = Nil
  var parsedString_annotated : List[(Int,String,Font,Double,Double,Int)] = Nil
  var wholewidth = 0
  var wholeheight = 0
  var maxheight = 0.0
  //private var text : String = ""
  //var size = new Rectangle2D.Double(0,0,0,0)

  /*
    def this(s : String) = {
      this()
      text_= s
    }
    */

    //def text() : String = text

    override def text_=(s : String) = {
      super.text = s
      //parsedString = List((0,"abc"),(-1,"def"),(-2,"ghi"),(1,"jkl"),(0,"ABC"))
      parsedString = List((0,"(could not parse"))
      val parsed = FormulaParser(s)
      if (parsed successful)
        parsedString = parsed get

      //self = new FormulaLabel
    }

    def createStringAnnotations(g:Graphics)  = {
      if (g != null) {
        val fontfactory = new FontFactory(g)

        parsedString_annotated = parsedString.map(_ match {case (size,string) =>
            val font = fontfactory getFont size
            val bounds : Rectangle2D = g.getFontMetrics(font).getStringBounds(string,g)
            val width  = bounds.getWidth
            val height = bounds.getHeight
            if (height > maxheight)
              maxheight = height
            val offset = -4 * size
            (size, string, font, width, height, offset) }
          )

        wholewidth = parsedString_annotated.map(_._4).reduceLeft(_+_).toInt
        wholeheight = maxheight.toInt
        val dim = new Dimension(wholewidth, 8*wholeheight )
        size_= (dim)
        preferredSize_= (dim)
        minimumSize_= (dim)

      }

    }

    override def paint(g:Graphics ) = {
      /*
      g setColor(new Color(200,50,180))
      g fillRect(r x , r y, r width, r height)
      g setColor (new Color(255,255,255))
      g drawLine (r.width/2, 0, r.width/2, r.height)
      g drawLine (0, r.height/2, r.width, r.height/2)
      g.drawRect(r.width/4,r.height/4, r.width/2, r.height/2)*/

      g.asInstanceOf[Graphics2D].setRenderingHint(
        RenderingHints.KEY_ANTIALIASING,
        RenderingHints.VALUE_ANTIALIAS_ON)

      g setColor(new Color(0,0,0))

      createStringAnnotations(g)
      var r = g getClipBounds ;

      //var x : Double = (r.width/2) - (wholewidth/2)
      //val y  = (r.height/2) - (wholeheight/2)
      var x = 0.0
      val y = wholeheight/2  

      /* this is only done for the side effects */
      parsedString_annotated.map(_ match {
        case (size, string, font, width, height, offset) =>
          g.setFont(font)
          val superscript_offset = if (offset<0) 0 else (maxheight / 2).toInt
          g.drawString(string, x.toInt ,y + superscript_offset + offset)
          x += width
      })

      //g.drawRect(r.width/2-minimumSize.width/2,r.height/2-minimumSize.height/2,
      //  minimumSize.width, minimumSize.height)

      //g.drawRect(0,0,wholewidth, wholeheight)
      //g.drawRect(r.x,r.y,r.width,r.height)


      println(minimumSize)
      
    }


  override def visible_=(b:Boolean) = {
    super.visible_=(b)                   
    if (b)
      createStringAnnotations(self.getGraphics)
  }
    
}

  


/*   */
object FormulaParser extends RegexParsers {
  val token = """[\^{}_]"""r
  val literal = """[^\^{}_]"""r

  def formula : Parser[String] = (parameter +) ^^ (
          (x:List[(Int,String)]) => { var str = ""; for(i <- x) { str += i._2 }; str }
          )

  def parameter : Parser[(Int,String)] = (
          literal ^^ (x=>(0,x)) |
          "{" ~> formula <~ "}" ^^ (x=>(0,x)) 
          )


  def annotated_formula : Parser[(Int,String)] = (
          formula ^^ ( x => (0,x) ) |
          "_" ~> parameter ^^ (x => (-1,x._2)) |
          "^" ~> parameter ^^ (x => ( 1,x._2)) 
          )

  def annotated_formulas = annotated_formula +

  def apply(s:String) = annotated_formulas(new CharSequenceReader(s))

  }




}