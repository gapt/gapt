package ch.randelshofer.tree.sunray;

import ch.randelshofer.tree.TreeNode;
import ch.randelshofer.tree.NodeInfo;
/*
 * @(#)SunrayModel.java  1.0  September 18, 2007
 *
 * Copyright (c) 2007 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

/**
 * SunrayModel manages a SunburstTree and its SunrayView.
 * 
 * 
 * @author Werner Randelshofer
 * @version 1.0 September 18, 2007 Created.
 */
public class SunrayModel {
    private SunrayTree tree;
    private NodeInfo info;
    
    /** Creates a new instance. */
    public SunrayModel(TreeNode root, NodeInfo info) {
        tree = new SunrayTree(root, info);
        this.info = info;
    }
    
    public SunrayView getView() {
        return new SunrayView(tree);
    }
    public NodeInfo getInfo() {
        return info;
    }
}
