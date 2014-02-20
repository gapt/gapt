/**
 * @(#)CirclemapNode.java  1.0  Jan 16, 2008
 *
 * Copyright (c) 2008 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.circlemap;

import ch.randelshofer.gui.ProgressObserver;
import ch.randelshofer.tree.TreeNode;
import ch.randelshofer.tree.NodeInfo;
import ch.randelshofer.tree.TreePath2;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

/**
 * The CirclemapNode class encapsulates a {@link TreeNode} whithin a
 * {@link CirclemapTree}.
 * <p>
 * It holds the radius of the data as an absolute value. 
 * The location is held relative to the center of the parent data.
 * <p>
 * This data can layout its subtree in a space-filling circular treemap.
 *
 * @author Werner Randelshofer
 * @version 1.0 Jan 16, 2008 Created.
 */
public class CirclemapNode extends Circle {
    private CirclemapNode parent;
    private TreePath2<TreeNode> dataNodePath;

    public CirclemapNode(CirclemapNode parent, TreeNode data) {
        this.parent = parent;
        this.dataNodePath = (parent == null) ? new TreePath2<TreeNode>(data) : parent.getDataNodePath().pathByAddingChild(data);
    }

    public List<CirclemapNode> children() {
        return Collections.EMPTY_LIST;
    }

    public boolean isLeaf() {
        return true;
    }

    public TreePath2<TreeNode> getDataNodePath() {
        return dataNodePath;
    }

    /** 
     * Lays out the subtree starting at this data in a space-filling 
     * circular treemap.
     */
    public void layout(NodeInfo info, ProgressObserver p) {
        radius = getWeightRadius(info);
    //radius = 1;
    }

    public double getWeightRadius(NodeInfo info) {
        return Math.max(1, Math.sqrt(info.getCumulatedWeight(dataNodePath) / Math.PI));
     }

    public CirclemapNode getParent() {
        return parent;
    }

    public TreeNode getDataNode() {
        return dataNodePath.getLastPathComponent();
    }
    
    @Override
    public String toString() {
        return this.getClass()+"[x:"+cx+",y:"+cy+",r:"+radius+"]";
//        return dataNodePath.getLastPathComponent().toString();
    }

    public int getDescendantCount() {
        return 0;
    }

    /** Updates the layout of all parent nodes.
     *
     * @param info
     */
    public void updateParentLayouts(NodeInfo info) {
        for (CirclemapNode n=getParent(); n!=null;n=n.getParent()) {
            CirclemapCompositeNode cn=(CirclemapCompositeNode)n;
            cn.updateNodeLayout(info);
        }
    }
}
