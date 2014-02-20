package ch.randelshofer.tree.sunray;

import ch.randelshofer.tree.TreeNode;
import ch.randelshofer.tree.NodeInfo;
/*
 * @(#)SunBurstTree.java  1.0  September 18, 2007
 *
 * Copyright (c) 2007 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

/**
 * IcerayModel manages a SunrayTree and its IcerayView.
 *
 * @author Werner Randelshofer
 * @version 1.0 September 18, 2007 Created.
 */
public class IcerayModel {
    private SunrayTree tree;
    private NodeInfo info;
    
    /** Creates a new instance. */
    public IcerayModel(TreeNode root, NodeInfo info) {
        this.info = info;
        tree = new SunrayTree(root, info, 8);
    }
    
    public IcerayView getView() {
        return new IcerayView(tree);
    }
    public NodeInfo getInfo() {
        return info;
    }
}
