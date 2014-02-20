/*
 * @(#)RectmapModel.java  1.0  2008-01-16
 *
 * Copyright (c) 2008 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.rectmap;

import ch.randelshofer.gui.ProgressObserver;
import ch.randelshofer.tree.TreeNode;
import ch.randelshofer.tree.NodeInfo;

/**
 * RectmapModel.
 * 
 * 
 * @author Werner Randelshofer
 * @version 1.0 2008-01-16 Created.
 */
public class RectmapModel {
    private RectmapTree tree;
    private NodeInfo info;
    
    /** Creates a new instance. */
    public RectmapModel(TreeNode root, NodeInfo info, ProgressObserver p) {
        tree = new RectmapTree(root, info, p);
        this.info = info;
    }
    
    public RectmapView getView() {
        return new RectmapView(tree);
    }
    public NodeInfo getInfo() {
        return info;
    }
}
