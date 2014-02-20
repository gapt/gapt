/*
 * @(#)LastModifiedByYearWeighter.java  1.0  2010-01-11
 * 
 * Copyright (c) 2010 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms..
 */

package ch.randelshofer.tree.demo;

import ch.randelshofer.tree.TreeNode;
import ch.randelshofer.tree.TreePath2;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import java.util.GregorianCalendar;

/**
 * LastModifiedByYearWeighter.
 *
 * @author Werner Randelshofer
 * @version 1.0 2010-01-11 Created.
 */
public class LastModifiedByYearWeighter extends LastModifiedWeighter {
    protected int minYear;
    protected int maxYear;
    protected int medianYear;
private GregorianCalendar cal=new GregorianCalendar();

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
//        new Date(min)
//        medianRecursive(root, valueList);
        if (dates.size() > 0) {
cal.setTimeInMillis(min);
minYear=cal.get(GregorianCalendar.YEAR);
cal.setTimeInMillis(max);
maxYear=cal.get(GregorianCalendar.YEAR);
cal.setTimeInMillis(median);
medianYear=cal.get(GregorianCalendar.YEAR);

            histogram = new int[maxYear-minYear+1];
            histogramRecursive(root); // XXX - Could be done without recursion, because we got all values now
        } else {
            histogram = new int[1];
            histogram[0] = 1;
        }
    }
    protected void histogramRecursive(TreeNode root) {
        FileNode fn = (FileNode) root;
        long lastModified = fn.getLastModified();
cal.setTimeInMillis(lastModified);
int lmYear=cal.get(GregorianCalendar.YEAR);

        int index = lmYear-minYear;
        histogram[index]++;

        for (TreeNode child : root.children()) {
            histogramRecursive(child);
        }
    }
    @Override
    public float getMedianWeight() {
        return (float) ((medianYear - minYear) /
                (float) (maxYear - minYear));
    }
    @Override
    public float getWeight(TreePath2 path) {
        TreeNode node = (TreeNode) path.getLastPathComponent();
        FileNode fn = (FileNode) node;
        long lastModified = fn.getLastModified();
cal.setTimeInMillis(lastModified);
int lmYear=cal.get(GregorianCalendar.YEAR);

        return (float) ((lmYear - minYear) /
                (float) (maxYear - minYear));
    }
    @Override
    public String getHistogramLabel(int index) {
        StringBuilder buf=new StringBuilder();
        buf.append("<html>");
        buf.append(minYear+index);
        buf.append("<br>");

        int totalCount=0;
        long totalSize=0;
        for (int i=0;i<histogram.length;i++) {
            totalCount+=histogram[i];
        }

        buf.append(intFormat.format(histogram[index]));
        buf.append(" Items (");
        buf.append(histogram[index]*100/totalCount);
        buf.append(" %)");
        return buf.toString();
    }

}
