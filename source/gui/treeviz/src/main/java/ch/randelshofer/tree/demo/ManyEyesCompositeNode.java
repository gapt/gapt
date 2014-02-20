/*
 * @(#)ManyEyesCompositeNode.java  1.0  2009-02-07
 * 
 * Copyright (c) 2009 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

package ch.randelshofer.tree.demo;

import ch.randelshofer.tree.TreeNode;
import java.util.*;

/**
 * ManyEyesCompositeNode.
 *
 * @author Werner Randelshofer, Staldenmattweg 2, CH-6410 Goldau
 * @version 1.0 2009-02-07 Created.
 */
public class ManyEyesCompositeNode extends ManyEyesNode {
    private ArrayList<ManyEyesNode> children = new ArrayList<ManyEyesNode>();

    public ManyEyesCompositeNode(String[] values) {
        super(values);
    }

    @Override
    public List<TreeNode> children() {
        return (children==null) ? Collections.EMPTY_LIST: children;
    }

    @Override
    public boolean getAllowsChildren() {
        return false;
    }
    public void removeAllChildren() {
            for (ManyEyesNode child : children) {
                child.parent=null;
            }
        children.clear();
    }

    public void add(ManyEyesNode child) {
        children.add(child);
        child.parent = this;
    }
    public void remove(ManyEyesNode child) {
        children.remove(child);
        child.parent = null;
    }


}
