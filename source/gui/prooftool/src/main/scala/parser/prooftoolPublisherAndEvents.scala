package at.logic.gui.prooftool.parser

/**
 * Created by IntelliJ IDEA.
 * User: mrukhaia
 * Date: Nov 5, 2010
 * Time: 3:00:53 PM
 */

import scala.swing.Publisher
import scala.swing.event.Event

object ProofToolPublisher extends Publisher

case object ProofDbChanged extends Event
case object ProofLoaded extends Event
case object ProofUnLoaded extends Event