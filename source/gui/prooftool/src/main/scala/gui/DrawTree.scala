package at.logic.gui.prooftool.gui

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: 2/6/11
 * Time: 1:38 PM
 */

import scala.swing._
import BorderPanel._
import java.awt.Font._
import at.logic.language.hol.HOLExpression
import at.logic.utils.ds.trees._

class DrawTree(private val struct: Tree[HOLExpression], private val fSize: Int) extends BorderPanel {
  background = new Color(255,255,255)
  opaque = false
 // val bd = Swing.MatteBorder(0,0,0,0, new Color(0,0,0))
  val ft = new Font(SANS_SERIF, PLAIN, fSize)
 // val labelFont = new Font(MONOSPACED, ITALIC, fSize-1)

  struct match {
    case tree: UnaryTree[HOLExpression] =>
      //border = Swing.EmptyBorder(0,0,0, fSize * 4)
      layout(new Label(tree.vertex.toString) { /* border = bd;*/ font = ft }) = Position.North
      layout(new DrawTree(tree.t, fSize)) = Position.Center
    case tree: BinaryTree[HOLExpression] =>
     // border = Swing.EmptyBorder(0,0,0, fSize * 4)
      layout(new Label(tree.vertex.toString) { /* border = bd; */ font = ft }) = Position.North
      layout(new DrawTree(tree.t1, fSize)) = Position.West
      layout(new Label("       ") {
        opaque = false
    //    font = labelFont
        verticalAlignment = Alignment.Top
      }) = Position.Center
      layout(new DrawTree(tree.t2, fSize)) = Position.East
    case tree: LeafTree[HOLExpression] => layout(new Label(struct.vertex.toString) { font = ft }) = Position.North
  }
}