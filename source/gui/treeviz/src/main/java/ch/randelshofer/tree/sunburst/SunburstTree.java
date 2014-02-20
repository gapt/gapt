/*
 * @(#)SunburstTree.java  1.0  September 18, 2007
 *
 * Copyright (c) 2007 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

package ch.randelshofer.tree.sunburst;

import ch.randelshofer.tree.TreeNode;
import ch.randelshofer.tree.NodeInfo;

/**
 * The SunburstTree class implements the model for the SunBurstTree.
 * It's a tree of SunburstNode, each keeping the
 * initial layout of the tree in the SunBurst's Model.
 * 
 * @author Werner Randelshofer
 * @version 1.0 September 18, 2007 Created.
 */
public class SunburstTree {
    private SunburstNode root;
    private NodeInfo info;
    
    /** Creates a new instance. */
    public SunburstTree(TreeNode root, NodeInfo info) {
        this.info = info;
        if (!root.getAllowsChildren()) {
            this.root = new SunburstNode(null, root);
        } else {
            this.root = new SunburstCompositeNode(null, root);
        }
        info.init(root);
        this.root.renumber(info);
        //this.root.dump();
    }
    
    public NodeInfo getInfo() {
        return info;
    }
    
    public SunburstNode getRoot() {
        return root;
    }
}
