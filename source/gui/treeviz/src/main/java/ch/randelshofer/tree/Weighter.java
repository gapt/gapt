/*
 * @(#)Weighter.java  1.1  2010-08-19
 *
 * Copyright (c) 2007-2010 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

package ch.randelshofer.tree;

/**
 * Weighter.
 *
 * @author Werner Randelshofer
 * @version 1.1 2010-08-19 Adds method getMedianWeight().
 * <br>1.0 September 26, 2007 Created.
 */
public interface Weighter {
    public void init(TreeNode root);
    
    public float getWeight(TreePath2 path);
    
    public int[] getHistogram();

    public String getHistogramLabel(int index);
    public String getMinimumWeightLabel();
    public String getMaximumWeightLabel();

    public float getMedianWeight();
}
