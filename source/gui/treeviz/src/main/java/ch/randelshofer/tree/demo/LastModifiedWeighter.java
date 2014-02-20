/*
 * @(#)LastModifiedWeighter.java  2.0  2008-01-27
 *
 * Copyright (c) 2007-2008 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.demo;

import ch.randelshofer.tree.TreeNode;
import ch.randelshofer.tree.TreePath2;
import ch.randelshofer.tree.Weighter;
import ch.randelshofer.text.FileSizeFormat;
import java.text.DateFormat;
import java.text.DecimalFormat;
import java.text.NumberFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;

/**
 * LastModifiedWeighter.
 *
 * @author Werner Randelshofer
 * @version 2.0 2008-01-27 Added computation and drawing of histogram. 
 * <br>1.0 September 26, 2007 Created.
 */
public class LastModifiedWeighter implements Weighter {

    protected long min = new Date(2003 - 1900, 0, 1).getTime();
    protected long max = new Date().getTime();
    protected long median = (max - min) / 2;
    protected int[] histogram;
    protected static FileSizeFormat shortWeightFormat;
    protected static NumberFormat intFormat = DecimalFormat.getIntegerInstance();

    /** Creates a new instance. */
    public LastModifiedWeighter() {
        shortWeightFormat = new FileSizeFormat();
        //shortWeightFormat.setShortFormat(true);
        shortWeightFormat.setMaximumFractionDigits(0);
    }

    public float getWeight(TreePath2 path) {
        TreeNode node = (TreeNode) path.getLastPathComponent();
        FileNode fn = (FileNode) node;
        long lastModified = fn.getLastModified();

        return (float) ((lastModified - min) /
                (float) (max - min));
    }

    public float getMedianWeight() {
        return (float) ((median - min) /
                (float) (max - min));
    }

    public void init(TreeNode root) {
        min = Long.MAX_VALUE;
        max = Long.MIN_VALUE;
        ArrayList<Long> dates = new ArrayList<Long>();
        collectDatesRecursive(root, dates);
        Collections.sort(dates);
        if (dates.size() > 0) {
            min = dates.get(0);
            max = dates.get(dates.size() - 1);
            median = dates.get(dates.size() / 2);
        }
//        medianRecursive(root, valueList);
        if (dates.size() > 0) {
            histogram = new int[256];
            histogramRecursive(root); // XXX - Could be done without recursion, because we got all values now
        } else {
            histogram = new int[1];
            histogram[0] = 1;
        }
    }

    protected void collectDatesRecursive(TreeNode node, java.util.List<Long> dates) {
        FileNode fn = (FileNode) node;
        long lastModified = fn.getLastModified();
        dates.add(lastModified);
        for (TreeNode child : node.children()) {
            collectDatesRecursive((TreeNode) child, dates);
        }
    }

    protected void histogramRecursive(TreeNode root) {
        FileNode fn = (FileNode) root;
        long lastModified = fn.getLastModified();

        int index = Math.min(histogram.length - 1, Math.max(0, (int) ((lastModified - min) * (histogram.length - 1) / (double) (max - min))));
        histogram[index]++;

        for (TreeNode child : root.children()) {
            histogramRecursive(child);
        }
    }

    public int[] getHistogram() {
        return histogram;
    }

    public String getMinimumWeightLabel() {
        return DateFormat.getDateTimeInstance().format(new Date(min));
    }

    public String getMaximumWeightLabel() {
        return DateFormat.getDateTimeInstance().format(new Date(max));
    }

    public String getHistogramLabel_old(int index) {
        if (max - min > 365*24*60*60*1000) {
       return DateFormat.getDateInstance().format(new Date((max - min) * index / histogram.length + min));
       } else {
       return DateFormat.getDateTimeInstance().format(new Date((max - min) * index / histogram.length + min));
       }
    }
    public String getHistogramLabel(int index) {
        StringBuilder buf=new StringBuilder();
        buf.append("<html>");
        if (max - min > 365*24*60*60*1000) {
       buf.append( DateFormat.getDateInstance().format(new Date((max - min) * index / histogram.length + min)));
       buf.append(" - ");
       buf.append( DateFormat.getDateInstance().format(new Date((max - min) * (index+1) / histogram.length + min)));
       } else {
       buf.append( DateFormat.getDateTimeInstance().format(new Date((max - min) * index / histogram.length + min)));
       buf.append(" - ");
       buf.append( DateFormat.getDateTimeInstance().format(new Date((max - min) * (index+1) / histogram.length + min)));
       }
        buf.append("<br>");
        buf.append(intFormat.format(histogram[index]));
        buf.append(" Items");
        return buf.toString();
    }
}
