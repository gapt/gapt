/**
 * @(#)CirclemapTree.java  1.2  2009-03-22
 *
 * Copyright (c) 2008-2009 Werner Randelshofer, Goldau, Switzerland.
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

/**
 * CirclemapTree lays out a tree structure in a space-filling circular treemap.
 *
 * @author Werner Randelshofer
 * @version 1.2 2009-03-22 Made layout progress observable.
 * <br>1.0 Jan 16, 2008 Created.
 */
public class CirclemapTree {

    private CirclemapNode root;
    private NodeInfo info;

    /** Creates a new instance. */
    public CirclemapTree(TreeNode root, NodeInfo info, ProgressObserver p) {
        p.setNote("Constructing tree…");
        this.info = info;
        if (!root.getAllowsChildren()) {
        this.root = new CirclemapNode(null, root);
        } else {
        this.root = new CirclemapCompositeNode(null, root);
        }
        info.init(root);
        long start = System.currentTimeMillis();
        p.setNote("Calculating layout…");
        p.setMaximum(p.getMaximum()+this.root.getDescendantCount());
        p.setIndeterminate(false);
        this.root.layout(info, p);
        long end = System.currentTimeMillis();
        System.out.println("CirclemapTree layout elapsed "+(end-start)+"ms");
    }

    public NodeInfo getInfo() {
        return info;
    }

    public CirclemapNode getRoot() {
        return root;
    }
}
