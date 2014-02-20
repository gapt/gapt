/**
 * @(#)CirclemapCompositeNode.java  1.1  2010-08-19
 *
 * Copyright (c) 2008-2010 Werner Randelshofer, Goldau, Switzerland.
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
import java.util.*;

/**
 * The CirclemapNode class encapsulates a composite {@link TreeNode} whithin a
 * {@link CirclemapTree}.
 *
 * @author Werner Randelshofer
 * @version 1.1 2010-08-19 Includes the weight of the composite node itself
 * into the size calculation of a circle.
 * <br>1.0 Jan 16, 2008 Created.
 */
public class CirclemapCompositeNode extends CirclemapNode {

    private int descendants = -1;
    private ArrayList<CirclemapNode> children;

    /** Creates a new instance. */
    public CirclemapCompositeNode(CirclemapNode parent, TreeNode node) {
        super(parent, node);

        children = new ArrayList<CirclemapNode>();
        for (TreeNode c : node.children()) {
            if (!c.getAllowsChildren()) {
                children.add(new CirclemapNode(this, c));
            } else {
                children.add(new CirclemapCompositeNode(this, c));
            }
        }
    }

    @Override
    public boolean isLeaf() {
        return false;
    }

    @Override
    public List<CirclemapNode> children() {
        return Collections.unmodifiableList(children);
    }

    @Override
    public void layout(NodeInfo info, ProgressObserver p) {
        if (p.isCanceled()) {
            return;
        }

        for (CirclemapNode child : children) {
            child.layout(info, p);
        }
        updateNodeLayout(info);
    }
    /** Updates the layout of this node only. Does not update the layout
     * of child nodes or parent nodes.
     *
     * @param info
     */
    public void updateNodeLayout(NodeInfo info) {
        if (children.size() == 0) {
            radius = Math.max(10, getWeightRadius(info));
            return;
        } else if (children.size() == 1) {
            radius = //children.get(0).radius + 1;
            radius = Math.max(children.get(0).radius + 1, getWeightRadius(info));
            return;
        }


        ArrayList<Circle> circles = new ArrayList<Circle>();
        circles.addAll(children);

        Circles.pairPack(circles);
        // Circles.phyllotacticPack(circles);

        Circle cbounds = Circles.boundingCircle(circles);
        radius = cbounds.radius;
        radius = Math.max(radius, getWeightRadius(info));
        for (CirclemapNode child : children) {
            child.cx -= cbounds.cx;
            child.cy -= cbounds.cy;
        }
    }

    @Override
    public int getDescendantCount() {
        if (descendants == -1) {
            descendants += children.size();
            for (CirclemapNode child : children) {
                descendants += child.getDescendantCount();
            }
        }
        return descendants;
    }

    /** Call this method when a new child node has been added to the underlying
     * TreeNode.
     * <p>
     * For performance reasons, this method will not update the layout of
     * the circlemap.
     *
     * @param c the new child
     * @return Returns the new CirclemapNode which holds the child.
     */
    public CirclemapNode newChildAdded(TreeNode c) {
        CirclemapNode cn;
        if (!c.getAllowsChildren()) {
            children.add(cn=new CirclemapNode(this, c));
        } else {
            children.add(cn=new CirclemapCompositeNode(this, c));
        }
        return cn;
    }
}
  
