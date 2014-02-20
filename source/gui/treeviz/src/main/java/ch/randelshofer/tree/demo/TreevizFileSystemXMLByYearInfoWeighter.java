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
import java.text.ParseException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Date;
import java.util.GregorianCalendar;
import java.util.Set;

/**
 * LastModifiedByYearWeighter.
 *
 * @author Werner Randelshofer
 * @version 1.0 2010-01-11 Created.
 */
public class TreevizFileSystemXMLByYearInfoWeighter extends TreevizFileSystemXMLInfoWeighter {
    protected int minYear;
    protected int maxYear;
    protected int medianYear;
private GregorianCalendar cal=new GregorianCalendar();

    /** Creates a new instance. */
    public TreevizFileSystemXMLByYearInfoWeighter(TreevizFileSystemXMLNodeInfo info, String key) {
        super(info,key);
    }

    TreevizFileSystemXMLByYearInfoWeighter(TreevizFileSystemXMLNodeInfo info, String colorAttribute, String sizeAttribute) {
        super(info, colorAttribute,sizeAttribute);
    }

    @Override
    public void init(TreeNode root) {
        if (info.getType(key) == AbstractNodeInfo.DataType.DATE_STRING) {
            Date minDate = new Date(Long.MAX_VALUE);
            Date maxDate = new Date(Long.MIN_VALUE);
            Set<String> stringValues = info.getValues(key);

            ArrayList<Date> dates = new ArrayList<Date>();
            collectDatesRecursive((TreevizFileSystemXMLNode) root, dates);
            Collections.sort(dates);
            if (dates.size() > 0) {
                minDate = dates.get(0);
                maxDate = dates.get(dates.size() - 1);
                median = dates.get(dates.size() / 2);
                min = minDate;
                max = maxDate;
            }

cal.setTime((Date)min);
minYear=cal.get(GregorianCalendar.YEAR);
cal.setTime((Date)max);
maxYear=cal.get(GregorianCalendar.YEAR);
cal.setTime((Date)median);
medianYear=cal.get(GregorianCalendar.YEAR);


            if (minYear!=maxYear) {

            histogram = new int[maxYear-minYear+1];
        sizeHistogram=new long[histogram.length];

            calculateDateHistogramRecursive(root); 


            } else {
                histogram = new int[1];
                histogram[0] = 1;
        sizeHistogram=new long[histogram.length];
            calculateDateHistogramRecursive(root);
            }
        } else {
            histogram = new int[1];
            histogram[0] = 1;
        sizeHistogram=new long[histogram.length];
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
    /*
    @Override
    public float getWeight(TreePath2 path) {
        TreeNode node = (TreeNode) path.getLastPathComponent();
        FileNode fn = (FileNode) node;
        long lastModified = fn.getLastModified();
cal.setTimeInMillis(lastModified);
int lmYear=cal.get(GregorianCalendar.YEAR);

        return (float) ((lmYear - minYear) /
                (float) (maxYear - minYear));
    }*/
    @Override
    public float getWeight(TreePath2 path) {
        TreevizFileSystemXMLNode node = (TreevizFileSystemXMLNode) path.getLastPathComponent();
        Object obj = node.getAttribute(key);
        String str = (obj != null) ? obj.toString() : null;
        if (str != null && min != null && max != null) {
            try {
                Date value;
                try {
                    value = (Date) isoDateFormatter.parse(str);

                } catch (ParseException ex) {
                    value = (Date) isoDateFormatter2.parse(str);
                }
cal.setTime(value);
int lmYear=cal.get(GregorianCalendar.YEAR);
        return (float) ((lmYear - minYear) /
                (float) (maxYear - minYear));
                //return (value.getTime() - ((Date) min).getTime()) / (float) (((Date) max).getTime() - ((Date) min).getTime());
            } catch (ParseException ex) {
            } catch (NumberFormatException ex) {
            } catch (ArrayIndexOutOfBoundsException ex) {
            }
        }
        return 0f;
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
            totalSize+=sizeHistogram[i];
        }

        buf.append(intFormat.format(histogram[index]));
        buf.append(" Items (");
        buf.append(histogram[index]*100/totalCount);
        buf.append(" %)<br>");
        buf.append(shortWeightFormat.format(sizeHistogram[index]));
        buf.append(" (");
        buf.append(sizeHistogram[index]*100/totalSize);
        buf.append(" %)");
        return buf.toString();
    }

}
