/*
 * @(#)XMLNode.java  1.0.1  2011-08-19
 *
 * Copyright (c) 2007-2011 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.demo;

import ch.randelshofer.tree.NodeInfo;
import ch.randelshofer.tree.TreeNode;
import ch.randelshofer.tree.TreePath2;
import java.util.*;

/**
 * XMLNode.
 *
 * @author  Werner Randelshofer
 * @version 2011-08-19 Composite nodes had weight +1 instead of correct weight.
 * <br>1.0 23. Juni 2008 Created.
 */
public class XMLNode implements TreeNode {

    private ArrayList<XMLNode> children;
    private String name;
    private HashMap<String, String> attributes;
    private long cumulatedWeight;

    /** Creates a new instance. */
    public XMLNode() {
        attributes = new HashMap<String, String>();
    }

    @Override
    public List<TreeNode> children() {
        return (children == null) ? Collections.EMPTY_LIST : children;
    }

    public void addChild(TreeNode child) {
        if (children == null) {
            children = new ArrayList<XMLNode>();
        }
        children.add((XMLNode) child);
    }

    @Override
    public boolean getAllowsChildren() {
        return children != null;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }


    public void putAttribute(String key, String value) {
        attributes.put(key, value);
    }

    public String getAttribute(String key) {
        return attributes.get(key);
    }

    public HashMap<String, String> getAttributes() {
        return attributes;
    }

    public long getCumulatedWeight() {
        return cumulatedWeight;
    }

    public void setCumulatedWeight(long newValue) {
        cumulatedWeight = newValue;
    }

    public void accumulateWeights(NodeInfo info, TreePath2 path) {
        TreePath2 myPath;
        if (path == null) {
            myPath = new TreePath2(this);
        } else {
            myPath = path.pathByAddingChild(this);
        }
        cumulatedWeight = info.getWeight(myPath);
        if (children != null) {
            cumulatedWeight=0;
            for (XMLNode child : children) {
                child.accumulateWeights(info, myPath);
                cumulatedWeight += child.getCumulatedWeight();
            }
        }
    }
}
