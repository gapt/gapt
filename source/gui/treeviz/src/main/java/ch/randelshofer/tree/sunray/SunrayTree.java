/*
 * @(#)SunrayTree.java  1.0  September 18, 2007
 *
 * Copyright (c) 2007 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

package ch.randelshofer.tree.sunray;

import ch.randelshofer.tree.TreeNode;
import ch.randelshofer.tree.NodeInfo;

/**
 * SunrayView provides an interactive user interface for a {@link SunrayTree}.
 * <p>
 * Supports rotation of the tree and zooming into a subtree.
 * 
 * 
 * @author Werner Randelshofer
 * @version 1.0 September 18, 2007 Created.
 */
public class SunrayTree {
    private SunrayNode root;
    private int maxScatter = 3;
    private NodeInfo info;
    
    /** Creates a new instance. */
    public SunrayTree(TreeNode root, NodeInfo info) {
        this(root, info, 4);
    }
    public SunrayTree(TreeNode root, NodeInfo info, int maxScatter) {
        this.info = info;
        if (!root.getAllowsChildren()) {
            this.root = new SunrayNode(null, root, 0);
        } else {
            this.root = new SunrayCompositeNode(null, root, 0);
        }
        info.init(root);
        this.root.renumber(maxScatter);
        //this.root.dump();
    }
    
    public NodeInfo getInfo() {
        return info;
    }
    
    public SunrayNode getRoot() {
        return root;
    }
}
