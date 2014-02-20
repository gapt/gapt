/*
 * @(#)SunrayCompositeNode.java  1.0  September 18, 2007
 *
 * Copyright (c) 2007 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

package ch.randelshofer.tree.sunray;

import ch.randelshofer.tree.TreeNode;
import java.util.*;
/**
 * SunrayCompositeNode.
 *
 *
 * @author Werner Randelshofer
 * @version 1.0 September 18, 2007 Created.
 */
public class SunrayCompositeNode extends SunrayNode {
    private ArrayList<SunrayNode> children;
    
    /** Creates a new instance. */
    public SunrayCompositeNode(SunrayNode parent, TreeNode node, int depth) {
        super(parent, node, depth);
        
        children = new ArrayList<SunrayNode>();
        for (TreeNode c : node.children()) {
            if (c.getAllowsChildren()) {
                children.add(new SunrayCompositeNode(this, c, depth + 1));
            }
        }
        for (TreeNode c : node.children()) {
            if (!c.getAllowsChildren()) {
                children.add(new SunrayNode(this, c, depth + 1));
            }
        }
    }
    
    public List<SunrayNode> children() {
        return Collections.unmodifiableList(children);
    }
    protected int renumber(int depth, int number, int scatter, int maxScatter, int maxDepth) {
        // System.out.println("SunrayNode.renumber "+depth+" "+number+" "+scatter+" "+maxScatter);
        this.maxScatter = maxScatter;
        this.totalScatter = maxDepth * maxScatter;
        if (children().size() == 0) {
            left = number++;
            right = number;
        } else {
            scatter = 0;
            left = number;
            for (SunrayNode child : children()) {
                if (! child.isLeaf() && scatter > 0) {
                    number++;
                }
                if (child.isLeaf()) {
                    number = child.renumber(depth + 1, number, scatter, maxScatter, maxDepth);
                    scatter = (scatter + 1) % totalScatter;
                } else {
                    number = child.renumber(depth + 1, number, scatter, maxScatter, maxDepth - 1);
                    scatter = 0;
                }
            }
            if (scatter != 0) {
                number += 1;
            }
            right = number;
        }
        return number;
    }
}
