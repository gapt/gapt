/*
 * @(#)SunburstCompositeNode.java  1.0  September 18, 2007
 *
 * Copyright (c) 2007 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

package ch.randelshofer.tree.sunburst;

import ch.randelshofer.tree.TreeNode;
import java.util.*;
/**
 * SunburstCompositeNode.
 * 
 * @author Werner Randelshofer
 * @version 1.0 September 18, 2007 Created.
 */
public class SunburstCompositeNode extends SunburstNode {
    private ArrayList<SunburstNode> children;
    
    /** Creates a new instance. */
    public SunburstCompositeNode(SunburstNode parent, TreeNode node) {
        super(parent, node);
        
        children = new ArrayList<SunburstNode>();
        for (TreeNode c : node.children()) {
            if (!c.getAllowsChildren()) {
                children.add(new SunburstNode(this, c));
            } else {
                children.add(new SunburstCompositeNode(this, c));
            }
        }
    }
    public List<SunburstNode> children() {
        return Collections.unmodifiableList(children);
    }
}
