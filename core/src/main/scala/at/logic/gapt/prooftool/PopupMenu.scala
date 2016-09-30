package at.logic.gapt.prooftool

import at.logic.gapt.proofs.{ DagProof, SequentProof }
import at.logic.gapt.proofs.lk.{ InitialSequent, LKProof }

import swing.SequentialContainer.Wrapper
import javax.swing.JPopupMenu

import swing._
import at.logic.gapt.expr._

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
            selected = dsp.collapsed
            action = Action( "Hide proof above" ) {
              if ( dsp.collapsed )
                dsp.main.publisher.publish( ShowSequentProof( dsp.pos ) )
              else
                dsp.main.publisher.publish( HideSequentProof( dsp.pos ) )
            }
          }
          contents += new MenuItem( Action( "View proof in new window" ) {
            prooftool( dsp.proof )
          } )
      }
    }
    popupMenu.show( dsp, x, y )
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

  def firstQuantifiers( f: HOLFormula ): List[HOLFormula] = f match {
    case HOLAtom( _, _ )          => Nil
    case And( l, r )              => firstQuantifiers( l ) ++ firstQuantifiers( r )
    case Imp( l, r )              => firstQuantifiers( l ) ++ firstQuantifiers( r )
    case Or( l, r )               => firstQuantifiers( l ) ++ firstQuantifiers( r )
    case Neg( l )                 => firstQuantifiers( l )
    case All( _, _ ) | Ex( _, _ ) => List( f )
  }
}

