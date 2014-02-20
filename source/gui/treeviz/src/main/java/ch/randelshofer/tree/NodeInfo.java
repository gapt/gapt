/*
 * @(#)NodeInfo.java  1.2  2011-01-11
 *
 * Copyright (c) 2007-2011 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree;

import java.awt.Color;
import java.awt.Image;
import java.util.List;
import javax.swing.Action;
import javax.swing.event.ChangeListener;

/**
 * NodeInfo is used to interpret the data stored in a {@link TreeNode}.
 * <p>
 * All methods of NodeInfo take a path to a node as a parameter. This allows
 * to get an interperation of a node based on more criteria than just on the
 * node alone.
 *
 * @author Werner Randelshofer
 * @version 1.2 2011-01-11 Adds support for actions.
 * <br>1.1 2008-07-04 Adds support for change listeners.
 * <br>1.0 September 21, 2007 Created.
 */
public interface NodeInfo {

    /**
     * Initializes the node info.
     * @param root
     */
    public void init(TreeNode root);

    /**
     * Returns the name of the node.
     */
    public String getName(TreePath2<TreeNode> path);

    /**
     * Returns the color of the node.
     */
    public Color getColor(TreePath2<TreeNode> path);

    /**
     * Returns the weight of a node.
     * @return The weight between 0 and Double.MAX_VALUE.
     */
    public long getWeight(TreePath2<TreeNode> path);

    /**
     * Returns the cumulated weight of a node (the sum of the weights of this
     * node and of all its children).
     * @return The weight between 0 and Double.MAX_VALUE.
     */
    public long getCumulatedWeight(TreePath2<TreeNode> path);

    /**
     * Returns the string formatted weight of a node.
     */
    public String getWeightFormatted(TreePath2<TreeNode> path);

    /**
     * Returns the tooltip of the node.
     */
    public String getTooltip(TreePath2<TreeNode> path);

    /** Returns actions for the specified node. 
     * @return An array of action objects. Returns an empty array if no
     * actions are available. Never returns null.
     */
    public Action[] getActions(TreePath2<TreeNode> path);
    /**
     * Returns the image of the node.
     */
    public Image getImage(TreePath2<TreeNode> path);

    public Weighter getWeighter();

    public Colorizer getColorizer();

    public void addChangeListener(ChangeListener l);

    public void removeChangeListener(ChangeListener l);

    public void toggleColorWeighter();

}
