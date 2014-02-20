/*
 * @(#)XMLNumericInfoWeighter.java  1.0  2010-08-19
 *
 * Copyright (c) 2010 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.demo;

import ch.randelshofer.tree.*;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

/**
 * XMLNumericInfoWeighter.
 *
 * @author  Werner Randelshofer
 * @version 1.0 2010-08-19 Created.
 */
public class XMLNumericInfoWeighter implements Weighter {

    private XMLNodeInfo info;
    private String key;
    private int[] histogram;
    private double min;
    private double max;
    private double median;

    /** Creates a new instance. */
    public XMLNumericInfoWeighter(XMLNodeInfo info, String key) {
        this.info = info;
        this.key = key;
    }

    @Override
    public void init(TreeNode root) {
        if (info.getType(key) == XMLNodeInfo.DataType.NUMERIC_STRING) {
            double minDate = Double.MAX_VALUE;
            double maxDate = Double.MIN_VALUE;
            Set<String> stringValues = info.getValues(key);

            ArrayList<Double> dates = new ArrayList<Double>();
            collectDatesRecursive((XMLNode) root, dates);
            Collections.sort(dates);
            if (dates.size() > 0) {
                minDate = dates.get(0);
                maxDate = dates.get(dates.size() - 1);
                median = dates.get(dates.size() / 2);
                min = minDate;
                max = maxDate;
            }

            if (maxDate != minDate) {
                histogram = new int[256];
                calculateDateHistogramRecursive(root);
            } else {
                histogram = new int[1];
                histogram[0] = 1;
            }
        } else {
            histogram = new int[1];
            histogram[0] = 1;
        }
    }

    private void collectDatesRecursive(XMLNode node, List<Double> dates) {
        String str = node.getAttribute(key);
        if (str != null) {
            double value;
            try {
                value = Double.parseDouble(str);
                dates.add(value);
            } catch (NumberFormatException ex) {
                // skip unparsable numbers
            }
        }
        for (TreeNode child : node.children()) {
            collectDatesRecursive((XMLNode) child, dates);
        }
    }

    /**
     * Calculates the date histogram recursively.
     * 
     * @param root
     */
    private void calculateDateHistogramRecursive(TreeNode root) {
        XMLNode node = (XMLNode) root;
        String str = node.getAttribute(key);
        if (str != null) {
            double value;
            try {
                value = Double.parseDouble(str);
                int index = Math.min(histogram.length - 1, Math.max(0, (int) ((value - ( min)) * (histogram.length - 1) /  (( max) - ( min)))));
                histogram[index]++;
            } catch (NumberFormatException ex) {
                // skip unparsable numbers
            }
        }
        for (TreeNode child : root.children()) {
            calculateDateHistogramRecursive(child);
        }
    }

    @Override
    public float getWeight(TreePath2 path) {
        XMLNode node = (XMLNode) path.getLastPathComponent();
        String str = node.getAttribute(key);
        if (str != null) {
            double value;
            try {
                value = Double.parseDouble(str);
                return (float)((value - ( min)) /  (( max) - ( min)));
            } catch (NumberFormatException ex) {
                // skip unparsable numbers
            }
        }
        return 0f;
    }

    @Override
    public int[] getHistogram() {
        return histogram;
    }

    private String toString(double d) {
        String str= Double.toString(d);
        if (str.endsWith(".0")) {
            str=str.substring(0,str.length()-2);
        }
        return str;
    }

    @Override
    public String getMinimumWeightLabel() {
        return toString(min);
    }

    @Override
    public String getMaximumWeightLabel() {
        return toString(max);
    }

    @Override
    public String getHistogramLabel(int index) {
        double precision = (max-min)/histogram.length;
        if (precision >= 1) {
        return toString(Math.round(min+((max-min)*index/histogram.length)));
        } else {
        return toString((min+((max-min)*index/histogram.length)));
        }
    }

    @Override
    public float getMedianWeight() {
        double value =  median;
        return (float) ((value - ( min)) / (( max) - ( min)));
    }
}
