package ch.randelshofer.tree.sunburst;

import ch.randelshofer.tree.TreeNode;
import ch.randelshofer.tree.NodeInfo;
/*
 * @(#)SunburstModel.java  1.0  September 18, 2007
 *
 * Copyright (c) 2007 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

/**
 * SunburstModel manages a SunburstTree and its SunburstView.
 * 
 * @author Werner Randelshofer
 * @version 1.0 September 18, 2007 Created.
 */
public class SunburstModel {
    private SunburstTree tree;
    private NodeInfo info;
    
    /** Creates a new instance. */
    public SunburstModel(TreeNode root, NodeInfo info) {
        tree = new SunburstTree(root, info);
        this.info = info;
    }
    
    public SunburstView getView() {
        return new SunburstView(tree);
    }
    public NodeInfo getInfo() {
        return info;
    }
}
