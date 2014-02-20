/**
 * @(#)RectmapNode.java  1.2  2009-03-22
 *
 * Copyright (c) 2008-2009 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.rectmap;

import ch.randelshofer.gui.ProgressObserver;
import ch.randelshofer.tree.*;
import java.awt.geom.Rectangle2D;
import java.util.Collections;
import java.util.List;

/**
 * The RectmapNode encapsulatets a {@link TreeNode} whithin a {@link RectmapTree}.
 * <p>
 * It holds the width and height of the node as an absolute value. 
 * The location is held relative to the location of the parent node.
 * <p>
 * This node can layout its subtree in a space-filling rectangular
 * treemap.
 *
 * @author Werner Randelshofer
 * @version 1.2 2009-03-22 Made layout progress observable.
 * <br>1.0 Jan 16, 2008 Created.
 */
public class RectmapNode extends Rectangle2D.Double {

    protected RectmapNode parent;
    protected TreePath2<TreeNode> dataNodePath;
    protected double cumulatedWeight = -1;

    public RectmapNode(RectmapNode parent, TreeNode data) {
        this.parent = parent;
        this.dataNodePath = (parent == null) ? new TreePath2<TreeNode>(data) : parent.getDataNodePath().pathByAddingChild(data);
    }

    public List<RectmapNode> children() {
        return Collections.EMPTY_LIST;
    }

    public boolean isLeaf() {
        return true;
    }
    public TreePath2<TreeNode> getDataNodePath() {
        return dataNodePath;
    }


    /** 
     * Lays out the subtree starting at this node in a space-filling 
     * rectangular treemap.
     * <p>
     * Note: You must call updateCumulatedWeight before you can layout a
     * node.
     * 
     */
    public void layout(ProgressObserver p) {
        if (parent == null) {
            width = height = Math.max(1, Math.sqrt(getCumulatedWeight()));
            x = y = 0;
        }
    }

    public RectmapNode getParent() {
        return parent;
    }

    public void updateCumulatedWeight(NodeInfo info) {
       cumulatedWeight = Math.max(1, info.getCumulatedWeight(dataNodePath));
    }
    public double getCumulatedWeight() {
        return cumulatedWeight;
    }
     public int getDescendantCount() {
        return 0;
    }
    @Override
   public String toString() {
        return dataNodePath.getLastPathComponent()+" [x:"+x+",y:"+y+",w:"+width+",h:"+height+"]";
    }
}
