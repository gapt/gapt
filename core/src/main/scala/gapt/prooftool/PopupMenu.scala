package gapt.prooftool

import gapt.expr._
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.InitialSequent
import gapt.proofs.DagProof
import gapt.proofs.SequentIndex
import gapt.proofs.SequentProof
import javax.swing.JPopupMenu

import scala.swing.SequentialContainer.Wrapper
import scala.swing._

class PopupMenu extends Component with Wrapper {
  override lazy val peer: JPopupMenu = new JPopupMenu

  def show( invoker: Component, x: Int, y: Int ) { peer.show( invoker.peer, x, y ) }
}

object PopupMenu {

  // PopupMenu for LKProofs.
  def apply[T <: DagProof[T]]( main: DagProofViewer[T], tproof: DagProof[T], component: Component, x: Int, y: Int ) {
    lazy val proof = tproof.asInstanceOf[LKProof]
    val popupMenu = new PopupMenu {
      contents += new MenuItem( Action( "Save Subproof as..." ) { /*main.fSave( ( proof.name, proof ) )*/ } )
    }
    popupMenu.show( component, x, y )
  }

  def apply[F, T <: SequentProof[F, T]]( dsp: DrawSequentProof[F, T], x: Int, y: Int ) {
    val popupMenu = new PopupMenu {
      contents += new MenuItem( Action( "View Subproof as Sunburst Tree" ) {
        dsp.main.initSunburstDialog( "subproof " + dsp.main.name, dsp.proof )
      } )

      dsp.proof match {
        case _: InitialSequent =>

        case _ =>
          contents += new Separator
          contents += new CheckMenuItem( "Hide proof above" ) {
            selected = dsp.aboveLinePanel match {
              case _: CollapsedSubproofsPanel[F, T] => true
              case _                                => false
            }
            action = Action( "Hide proof above" ) {
              dsp.aboveLinePanel match {
                case _: CollapsedSubproofsPanel[F, T] => dsp.main.publisher.publish( ShowSequentProof( dsp.pos ) )
                case _                                => dsp.main.publisher.publish( HideSequentProof( dsp.pos ) )
              }
            }
            contents += new MenuItem( Action( "View proof in new window" ) {
              dsp.proof match {
                case p: LKProof            => prooftool( p )
                case p: SequentProof[F, T] => prooftool( p )
              }
            } )
          }
      }
    }
    popupMenu.show( dsp, x, y )
  }

  /**
   * A popup menu for individual formulas in a sequent proof.
   * @param main The main window that contains this menu.
   * @param lbl The label that spawned the menu.
   * @param pos The position of the sequent in which lbl resides.
   * @param i The index of lbl within its sequent.
   */
  def apply[F, T <: SequentProof[F, T]]( main: SequentProofViewer[F, T], lbl: LatexLabel, pos: List[Int],
                                         i: SequentIndex, x: Int, y: Int ): Unit = {
    val popupMenu = new PopupMenu {
      contents += new MenuItem( Action( "Mark ancestors" ) {
        main.markAncestors( pos, Set( i ) )
      } )
      contents += new MenuItem( Action( "Mark descendants" ) {
        main.markDescendants( pos, Set( i ) )
      } )

      contents += new MenuItem( Action( "Mark ancestors & descendants" ) {
        main.markAncestorsAndDescendants( pos, Set( i ) )
      } )
    }

    popupMenu.show( lbl, x, y )
  }

  // PopupMenu for Expansion Trees.
  def apply( det: DrawETQuantifierBlock, component: Component, x: Int, y: Int ) {
    val popupMenu = new PopupMenu {
      contents += new MenuItem( Action( "Close" ) { det.close() } )
      contents += new MenuItem( Action( "Open" ) { det.open() } )
      contents += new MenuItem( Action( "Expand" ) { det.expand() } )
    }
    popupMenu.show( component, x, y )
  }

  // PopupMenu for the title label of either cedent
  def apply( main: ExpansionSequentViewer, ced: CedentPanel, x: Int, y: Int ) {
    val popupMenu = new PopupMenu {
      val trees = ced.treeList.drawnTrees
      contents += new MenuItem( Action( "Close all" ) { trees.foreach( det => det.closeAll() ) } )
      contents += new MenuItem( Action( "Open all" ) { trees.foreach( det => det.openAll() ) } )

      contents += new MenuItem( Action( "Expand all" ) { trees.foreach( det => det.expandAll() ) } )
      contents += new MenuItem( Action( "Reset" ) {
        ced.treeList = new TreeListPanel( main, ced.cedent )
        ced.scrollPane.contents = ced.treeList
        ced.revalidate()
      } )
    }
    popupMenu.show( ced.titleLabel, x, y )
  }

  def firstQuantifiers( f: Formula ): List[Formula] = f match {
    case Atom( _, _ )             => Nil
    case And( l, r )              => firstQuantifiers( l ) ++ firstQuantifiers( r )
    case Imp( l, r )              => firstQuantifiers( l ) ++ firstQuantifiers( r )
    case Or( l, r )               => firstQuantifiers( l ) ++ firstQuantifiers( r )
    case Neg( l )                 => firstQuantifiers( l )
    case All( _, _ ) | Ex( _, _ ) => List( f )
  }
}

