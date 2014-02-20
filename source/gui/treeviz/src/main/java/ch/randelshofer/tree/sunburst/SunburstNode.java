/*
 * @(#)SunburstNode.java  1.0  September 18, 2007
 *
 * Copyright (c) 2007 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

package ch.randelshofer.tree.sunburst;

import ch.randelshofer.tree.*;
import java.util.*;

/**
 * The SunburstNode encapsulatets a {@link TreeNode} whithin a {@link SunburstTree}.
 * <p>
 * It holds the computed left, right and depth value of a data.
 * 
 * @author Werner Randelshofer
 * @version 1.0 September 18, 2007 Created.
 */
public class SunburstNode {
    private SunburstNode parent;
    
    private TreePath2<TreeNode> dataNodePath;
    /**
     * Nested Sets Tree: left preorder sequence number.
     */
    private long left;
    /**
     * Nested Sets Tree: right preorder sequence number.
     */
    private long right;
    
    private int maxDepth = -1;
    
    /** Creates a new instance. */
    public SunburstNode(SunburstNode parent, TreeNode data) {
        this.dataNodePath = (parent == null) ? new TreePath2<TreeNode>(data) : parent.getDataNodePath().pathByAddingChild(data);
        this.parent = parent;
    }
    
    public TreeNode getNode() {
        return dataNodePath.getLastPathComponent();
    }
    public TreePath2<TreeNode> getDataNodePath() {
        return dataNodePath;
    }
    
    public int getMaxDepth() {
        if (maxDepth == -1) {
        maxDepth = getMaxDepth(this, 1);
        } 
        return maxDepth;
    }
    private int getMaxDepth(SunburstNode node, int depth) {
        int max = depth;
        for (SunburstNode child : node.children()) {
            max = Math.max(max, getMaxDepth(child, depth + 1));
        }
        return max;
    }
    
    public void renumber(NodeInfo info) {
        renumber(info, 0, 0);
    }
    
    private int renumber(NodeInfo info, int depth, int number) {
        if (children().size() == 0) {
            left = number++;
            //number += (int) (100 * info.getWeight(data));
            right = number;
        } else {
            left = number;
            for (SunburstNode child : children()) {
                number = child.renumber(info, depth + 1, number);
            }
            right = number;
        }
        return number;
    }
    
    public List<SunburstNode> children() {
        return Collections.EMPTY_LIST;
    }
    
    public void dump() {
        System.out.println(getDepth()+","+left+","+right+" "+toString());
        for (SunburstNode child : children()) {
            child.dump();
        }
    }
    
    public boolean isLeaf() {
        return !dataNodePath.getLastPathComponent().getAllowsChildren();
    }
    
    public long getLeft() {
        return left;
    }
    public long getRight() {
        return right;
    }
    public long getExtent() {
        return right - left;
    }
          
    
    public int getDepth() {
        return dataNodePath.getPathCount();
    }
    
    public boolean isDescendant(SunburstNode node) {
        return node.getLeft() >= getLeft() &&
                node.getRight() <= getRight() &&
                node.getDepth() >= getDepth();
    }

    public SunburstNode findNode(int depth, long number) {
        if (getLeft() <= number && getRight() > number) {
            if (depth == 0) {
                return this;
            } else {
                for (SunburstNode child : children()) {
                    SunburstNode found = child.findNode(depth - 1, number);
                    if (found != null) {
                        return found;
                    }
                }
            }
        }
        return null;
    }
}
