/**
 * @(#)RectmapTree.java  1.2  2009-03-22
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
import ch.randelshofer.tree.TreeNode;
import ch.randelshofer.tree.NodeInfo;

/**
 * RectmapTree lays out a tree structure in a space-filling rectangular treemap.
 *
 * @author Werner Randelshofer
 * @version 1.2 2009-03-22 Made layout progress observable.
 * <br>1.0 Jan 16, 2008 Created.
 */
public class RectmapTree {

    private RectmapNode root;
    private NodeInfo info;

    /** Creates a new instance. */
    public RectmapTree(TreeNode root, NodeInfo info, ProgressObserver p) {
        p.setNote("Constructing tree…");
        this.info = info;
        if (!root.getAllowsChildren()) {
        this.root = new RectmapNode(null, root);
        } else {
        this.root = new RectmapCompositeNode(null, root);
        }
        info.init(root);
        this.root.updateCumulatedWeight(info);
        p.setNote("Calculating layout…");
        p.setMaximum(p.getMaximum()+this.root.getDescendantCount());
        p.setIndeterminate(false);
        this.root.layout(p);
    }

    public NodeInfo getInfo() {
        return info;
    }

    public RectmapNode getRoot() {
        return root;
    }
}
