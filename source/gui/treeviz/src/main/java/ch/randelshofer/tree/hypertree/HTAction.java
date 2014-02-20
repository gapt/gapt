/*
 * HTAction.java
 *
 * www.bouthier.net
 * 2001
 */
package ch.randelshofer.tree.hypertree;

import ch.randelshofer.tree.NodeInfo;
import ch.randelshofer.tree.TreePath2;
import java.awt.event.*;
import javax.swing.Action;
import javax.swing.JComponent;
import javax.swing.JPopupMenu;

/**
 * The HTAction class manage the action on the hypertree :
 * drag of a node...
 */
public class HTAction
        extends MouseAdapter
        implements MouseMotionListener {

    private HTDraw model = null; // the drawing model
    private HTCoordE startPoint = null; // starting point of dragging
    private HTCoordE endPoint = null; // ending point of dragging
    private HTCoordS clickPoint = null; // clicked point

    /* --- Constructor --- */
    /**
     * Constructor.
     *
     * @param model    the drawing model
     */
    HTAction(HTDraw model) {
        this.model = model;
        startPoint = new HTCoordE();
        endPoint = new HTCoordE();
        clickPoint = new HTCoordS();
    }


    /* --- MouseAdapter --- */
    /**
     * Called when a user pressed the mouse button
     * on the hyperbolic tree.
     * Used to get the starting point of the drag.
     *
     * @param e    the MouseEvent generated when clicking
     */
    @Override
    public void mousePressed(MouseEvent e) {
        if (e.isPopupTrigger()) {
            showPopup(e);
        } else {
            if (e.isShiftDown()) {
                model.fastMode(true);
            }
            startPoint.projectionStoE(e.getX(), e.getY(),
                    model.getSOrigin(),
                    model.getSMax());
        }
    }

    /**
     * Called when a user release the mouse button
     * on the hyperbolic tree.
     * Used to signal the end of the translation.
     *
     * @param e    not used here
     */
    @Override
    public void mouseReleased(MouseEvent e) {
        if (e.isPopupTrigger()) {
            showPopup(e);
        } else {
            if (model.isAdjusting()) {
                model.setAdjusting(false);
                model.repaint();
            }

            model.fastMode(false);
            model.endTranslation();
        }
    }

    /**
     * Called when a user clicked on the hyperbolic tree.
     * Used to put the corresponding node (if any) at the
     * center of the hyperbolic tree.
     *
     * @param e    the MouseEvent generated when clicking
     */
    @Override
    public void mouseClicked(MouseEvent e) {
        if (e.getButton() == MouseEvent.BUTTON1) {
            if (e.isShiftDown()) {
                model.restore();
            } else {
                clickPoint.x = e.getX();
                clickPoint.y = e.getY();

                HTDrawNode node = model.findNode(clickPoint);
                if (node != null) {
                    model.translateToOrigin(node);
                }
            }
        }
    }


    /* --- MouseMotionListener --- */
    /**
     * Called when a used drag the mouse on the hyperbolic tree.
     * Used to translate the hypertree, thus moving the focus.
     *
     * @param e    the MouseEvent generated when draging
     */
    @Override
    public void mouseDragged(MouseEvent e) {
        // BEGIN PATCH Performance 
        model.setAdjusting(true);
        // END PATCH Performance 

        if (startPoint.isValid()) {
            endPoint.projectionStoE(e.getX(), e.getY(),
                    model.getSOrigin(),
                    model.getSMax());
            if (endPoint.isValid()) {
                model.translate(startPoint, endPoint);
            }
        }
    }

    /**
     * Called when the mouse mouve into the hyperbolic tree.
     * Not used here.
     *
     * @param e    the MouseEvent generated when mouving
     */
    @Override
    public void mouseMoved(MouseEvent e) {
    }

    // BEGIN PATCH Actions
    private void showPopup(MouseEvent evt) {
        HTDrawNode node = model.findNode(new HTCoordS(evt.getX(),evt.getY()));
        if (node != null) {
            TreePath2 path = node.getHTModelNode().getDataNodePath();
            Action[] a = model.getModel().getInfo().getActions(path);
            if (a.length > 0) {
                JPopupMenu m = new JPopupMenu();
                for (int i = 0; i < a.length; i++) {
                    m.add(a[i]);
                }
                m.show((JComponent) evt.getSource(), evt.getX(), evt.getY());
            }
        }
    }
    // END PATCH Actions
}

