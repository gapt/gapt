/**
 * @(#)DefaultNodeInfo.java  1.0  Jan 26, 2008
 *
 * Copyright (c) 2008 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree;

import java.awt.Color;
import java.awt.Image;
import java.text.DecimalFormat;
import javax.swing.Action;
import javax.swing.event.*;

/**
 * DefaultNodeInfo.
 *
 * @author Werner Randelshofer
 * @version 1.0 Jan 26, 2008 Created.
 */
public class DefaultNodeInfo implements NodeInfo {
    private EventListenerList listenerList = new EventListenerList();
    private ChangeEvent changeEvent;

    @Override
    public String getName(TreePath2<TreeNode> path) {
        return path.getLastPathComponent().toString();
    }

    @Override
    public Color getColor(TreePath2<TreeNode> path) {
        return Color.black;
    }

    @Override
    public long getWeight(TreePath2<TreeNode> path) {
        return 1;
    }

    @Override
    public String getTooltip(TreePath2<TreeNode> path) {
        StringBuilder buf = new StringBuilder();

        TreePath2<TreeNode> parentPath = path;
        do {
            buf.insert(0, "<br>");
            buf.insert(0, getName(parentPath));
            parentPath = parentPath.getParentPath();
        } while (parentPath != null);
        buf.insert(0, "<html>");
        buf.append("<br>");

        TreeNode node = path.getLastPathComponent();
        if (node.getAllowsChildren()) {
            buf.append(DecimalFormat.getIntegerInstance().format(node.children().size()));
            buf.append(" Files");
            buf.append("<br>");
        }

        long w = getWeight(path);
        buf.append(DecimalFormat.getIntegerInstance().format(w));
        return buf.toString();
    }

    @Override
    public Image getImage(TreePath2<TreeNode> path) {
        return null;
    }

    @Override
    public void init(TreeNode root) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public Weighter getWeighter() {
        return null;
    }

    @Override
    public Colorizer getColorizer() {
        return null;
    }
    @Override
    public void addChangeListener(ChangeListener l) {
        listenerList.add(ChangeListener.class,l);
    }
    
    /** Removes a change listener from the button. */
    @Override
    public void removeChangeListener(ChangeListener l) {
        listenerList.remove(ChangeListener.class,l);
    }
        /*
         * Notify all listeners that have registered interest for
         * notification on this event type.  The event instance
         * is lazily created using the parameters passed into
         * the fire method.
         *
         * @see EventListenerList
         */
    protected void fireStateChanged() {
        // Guaranteed to return a non-null array
        Object[] listeners = listenerList.getListenerList();
        // Process the listeners last to first, notifying
        // those that are interested in this event
        for (int i = listeners.length-2; i >= 0; i -= 2) {
            if (listeners[i]==ChangeListener.class) {
                // Lazily create the event:
                if (changeEvent == null) {
                    changeEvent = new ChangeEvent(this);
                }
                ((ChangeListener) listeners[i+1]).stateChanged(changeEvent);
            }
        }
    }

    @Override
    public String getWeightFormatted(TreePath2<TreeNode> path) {
        return DecimalFormat.getIntegerInstance().format(getWeight(path));
    }

    @Override
    public void toggleColorWeighter() {
        // do nothing
    }

    @Override
    public long getCumulatedWeight(TreePath2<TreeNode> path) {
        return getWeight(path);
    }

    @Override
    public Action[] getActions(TreePath2<TreeNode> path) {
        return new Action[0];
    }

}
