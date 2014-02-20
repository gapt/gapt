/*
 * @(#)ManyEyesNode.java  1.0  2009-02-07
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
import java.util.Collections;
import java.util.List;

/**
 * ManyEyesNode.
 *
 * @author Werner Randelshofer, Staldenmattweg 2, CH-6410 Goldau
 * @version 1.0 2009-02-07 Created.
 */
public class ManyEyesNode implements TreeNode {
    protected ManyEyesCompositeNode parent;
    private String name;
    private String[] values;
    private long weight;

    public ManyEyesNode(String[] values) {
        this.values = values;
    }

    public String[] getValues() {
        return values;
    }

    public ManyEyesCompositeNode getParent() {
        return parent;
    }
    public void setName(String newValue) {
        this.name=newValue;
    }
    public String getName() {
        return name;
    }

    public List<TreeNode> children() {
        return Collections.EMPTY_LIST;
    }

    public boolean getAllowsChildren() {
        return false;
    }

    public long getWeight() {
        return weight;
    }
    public void setWeight(long newValue) {
        this.weight = newValue;
    }
}
