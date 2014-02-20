/*
 * @(#)TreevizFileSystemXMLNode.java  1.0  4. Juli 2008
 *
 * Copyright (c) 2008 Werner Randelshofer, Goldau, Switzerland.
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
 * TreevizFileSystemXMLNode.
 *
 * @author  Werner Randelshofer
 * @version 1.0 4. Juli 2008 Created.
 */
public class TreevizFileSystemXMLNode implements TreeNode {

    private ArrayList<TreevizFileSystemXMLNode> children;
    private String name;
    private HashMap<String, Object> attributes;
    private long cumulatedWeight;
    private int descendants = -1;

    /** Creates a new instance. */
    public TreevizFileSystemXMLNode() {
        attributes = new HashMap<String, Object>();
    }

    public List<TreeNode> children() {
        return (children == null) ? Collections.EMPTY_LIST : children;
    }

    public void addChild(TreeNode child) {
        if (children == null) {
            children = new ArrayList<TreevizFileSystemXMLNode>();
        }
        children.add((TreevizFileSystemXMLNode) child);
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

    public void putAttribute(String key, Object value) {
        attributes.put(key, value);
    }

    public Object getAttribute(String key) {
        return attributes.get(key);
    }

    public HashMap<String, Object> getAttributes() {
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
            for (TreevizFileSystemXMLNode child : children) {
                child.accumulateWeights(info, myPath);
                cumulatedWeight += child.getCumulatedWeight();
            }
        }
    }

    public int getDescendantCount() {
        if (descendants == -1) {
            descendants = 0;
            if (children != null) {
                descendants += children.size();
                for (TreevizFileSystemXMLNode child : children) {
                    descendants += child.getDescendantCount();
                }
            }
        }
        return descendants;
    }
}
