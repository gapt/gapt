/*
 * @(#)XMLStringInfoWeighter.java  1.0  2010-10-17
 * 
 * Copyright © 2010 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms..
 */

package ch.randelshofer.tree.demo;

import ch.randelshofer.tree.*;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

/**
 * {@code XMLStringInfoWeighter} weights string by the char code of the
 * first character.
 *
 * @author Werner Randelshofer
 * @version 1.0 2010-10-17 Created.
 */
class XMLStringInfoWeighter  implements Weighter {

    private XMLNodeInfo info;
    private String key;
    private int[] histogram;
    private char min;
    private char max;
    private char median;

    /** Creates a new instance. */
    public XMLStringInfoWeighter(XMLNodeInfo info, String key) {
        this.info = info;
        this.key = key;
    }

    @Override
    public void init(TreeNode root) {
        if (info.getType(key) == XMLNodeInfo.DataType.NUMERIC_STRING) {
            char minChar = '\uffff';
            char maxChar = '\u0000';
            Set<String> stringValues = info.getValues(key);

            ArrayList<Character> chars = new ArrayList<Character>();
            collectCharactersRecursive((XMLNode) root, chars);
            Collections.sort(chars);
            if (chars.size() > 0) {
                minChar = chars.get(0);
                maxChar = chars.get(chars.size() - 1);
                median = chars.get(chars.size() / 2);
                min = minChar;
                max = maxChar;
            }

            if (maxChar != minChar) {
                histogram = new int[256];
                calculateHistogramRecursive(root);
            } else {
                histogram = new int[1];
                histogram[0] = 1;
            }
        } else {
            histogram = new int[1];
            histogram[0] = 1;
        }
    }

    private void collectCharactersRecursive(XMLNode node, List<Character> chars) {
        String str = node.getAttribute(key);
        if (str != null && str.length()>0) {
            char value;
            try {
                value = str.charAt(0);
                chars.add(value);
            } catch (NumberFormatException ex) {
                // skip unparsable numbers
            }
        }
        for (TreeNode child : node.children()) {
            collectCharactersRecursive((XMLNode) child, chars);
        }
    }

    /**
     * Calculates the date histogram recursively.
     *
     * @param root
     */
    private void calculateHistogramRecursive(TreeNode root) {
        XMLNode node = (XMLNode) root;
        String str = node.getAttribute(key);
        if (str != null && str.length()>0) {
            char value;
            try {
                value = str.charAt(0);
                int index = Math.min(histogram.length - 1, Math.max(0, (int) ((value - ( min)) * (histogram.length - 1) /  (( max) - ( min)))));
                histogram[index]++;
            } catch (NumberFormatException ex) {
                // skip unparsable numbers
            }
        }
        for (TreeNode child : root.children()) {
            calculateHistogramRecursive(child);
        }
    }

    @Override
    public float getWeight(TreePath2 path) {
        if (min==max) return 1f;

        XMLNode node = (XMLNode) path.getLastPathComponent();
        String str = node.getAttribute(key);
        if (str != null && str.length()>0) {
            char value;
            try {
                value = str.charAt(0);
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

