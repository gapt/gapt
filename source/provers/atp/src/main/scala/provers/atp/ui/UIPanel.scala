/*
 * UIPanel.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.ui

import at.logic.calculi.lk.base.Sequent
import at.logic.provers.atp.commands._

trait UIPanel[V <: Sequent] {
  def getNextCommand(com:Command, elements: Option[Iterator[V]]): Command
}
