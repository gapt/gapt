/*
 * @(#)ManyEyesNodeInfo.java  1.0  2009-02-07
 * 
 * Copyright (c) 2009 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.demo;

import ch.randelshofer.tree.Colorizer;
import ch.randelshofer.tree.TreeNode;
import ch.randelshofer.tree.TreePath2;
import ch.randelshofer.tree.Weighter;
import java.awt.Color;
import java.awt.Image;
import java.util.*;
import javax.swing.Action;
import javax.swing.event.ChangeListener;

/**
 * ManyEyesNodeInfo.
 *
 * @author Werner Randelshofer, Staldenmattweg 2, CH-6410 Goldau
 * @version 1.0 2009-02-07 Created.
 */
public class ManyEyesNodeInfo extends AbstractNodeInfo {

    private ManyEyesTree tree;
    private HashMap<String, DataType> types;
    private HashMap<String, HashSet<String>> attributes;
    /** Index of the weight attribute. The value -1 indicates that
     * we have none.
     */
    private int weightAttributeIndex = -1;
    /** Index of the color attribute. The value -1 indicates that
     * we have none.
     */
    private int colorAttributeIndex = -1;
    /**
     * The path indices are the first text values.
     * @param tree
     */
    private int[] pathIndices = null;

    public ManyEyesNodeInfo(ManyEyesTree tree) {
        this.tree = tree;
    }

    @Override
    public void init(TreeNode root) {
        types = new HashMap<String, DataType>();
        attributes = new HashMap<String, HashSet<String>>();
        computeBasicStats(tree.getNodes(), types, attributes);
    }

    public void computeBasicStats(ArrayList<ManyEyesNode> nodes, HashMap<String, DataType> typeMap, HashMap<String, HashSet<String>> attrMap) {
        collectAttributes(nodes, attrMap);
        for (Map.Entry<String, HashSet<String>> entry : attrMap.entrySet()) {
            typeMap.put(entry.getKey(), determineDataType(entry.getValue()));
        }

        String[] headers = tree.getHeaders();

        // The weight attribute is the first one with a numeric value
        weightAttributeIndex = -1;
        for (int i = 0; i < headers.length; i++) {
            if (typeMap.get(headers[i]) == DataType.NUMERIC_STRING) {
                weightAttributeIndex = i;
                break;
            }
        }
        // The color attribute is a data field after the weight attribute with
        // a numeric or date value or color value.
        colorAttributeIndex = -1;
        for (int i = weightAttributeIndex + 1; i < headers.length; i++) {
            if (typeMap.get(headers[i]) == DataType.NUMERIC_STRING
                    || typeMap.get(headers[i]) == DataType.DATE_STRING
                     || typeMap.get(headers[i]) == DataType.COLOR_STRING) {
                colorAttributeIndex = i;
                break;
            }
        }

        // Determine the path indices
        int length = 1;
        for (; length < headers.length && typeMap.get(headers[0]) == typeMap.get(headers[length]); length++) {
        }
        int[] indices = new int[length];
        for (int i = 0; i < length; i++) {
            indices[i] = i;
        }
        if (!Arrays.equals(indices, tree.getPathIndices())) {
            tree.createTreeStructure(indices);
        }

    }

    public void collectAttributes(ArrayList<ManyEyesNode> nodes, HashMap<String, HashSet<String>> attrMap) {
        String[] headers = tree.getHeaders();
        for (int i = 0; i < headers.length; i++) {
            HashSet<String> valueSet;
            valueSet = new HashSet<String>();
            attrMap.put(headers[i], valueSet);
        }

        for (ManyEyesNode node : nodes) {
            String[] values = node.getValues();
            for (int i = 0; i < headers.length; i++) {
                HashSet<String> valueSet;
                valueSet = attrMap.get(headers[i]);
                valueSet.add(values[i]);
            }
        }
    }

    @Override
    public String getName(TreePath2<TreeNode> path) {
        ManyEyesNode node = (ManyEyesNode) path.getLastPathComponent();
        return node.getName();
    }

    @Override
    public Color getColor(TreePath2<TreeNode> path) {
        return Color.GRAY;
    }

    @Override
    public long getCumulatedWeight(TreePath2<TreeNode> path) {
        return getWeight(path);
    }

    @Override
    public long getWeight(TreePath2<TreeNode> path) {
        if (weightAttributeIndex == -1) {
            return 1;
        } else {
            ManyEyesNode node = (ManyEyesNode) path.getLastPathComponent();
            String[] values = node.getValues();
            try {
                return Long.valueOf(values[weightAttributeIndex]);
            } catch (NumberFormatException e) {
                return 1;
            }
        }
    }

    @Override
    public String getWeightFormatted(TreePath2<TreeNode> path) {
        return ((Long) getWeight(path)).toString();
    }

    @Override
    public String getTooltip(TreePath2<TreeNode> path) {
        ManyEyesNode node = (ManyEyesNode) path.getLastPathComponent();

        StringBuilder buf = new StringBuilder();
        TreePath2<TreeNode> parentPath = path;
        // if (! node.getAllowsChildren()) {
        buf.insert(0, "</b><br>");
        buf.insert(0, getName(parentPath));
        buf.insert(0, "<b>");
        //  }
        parentPath = parentPath.getParentPath();
        while (parentPath != null && parentPath.getPathCount() > 1) {
            buf.insert(0, "<br>");
            buf.insert(0, getName(parentPath));
            parentPath = parentPath.getParentPath();
        }
        buf.insert(0, "<html>");


        String[] headers = tree.getHeaders();
        int[] pathIndices = tree.getPathIndices();
        String[] values = node.getValues();
        OuterLoop:
        for (int i = 0; i < headers.length; i++) {
            for (int j = 0; j < pathIndices.length; j++) {
                if (i == pathIndices[j]) {
                    continue OuterLoop;
                }
            }
            buf.append("<br>")//
                    .append(headers[i])//
                    .append(": ")//
                    .append(values[i]);
        }

        return buf.toString();
    }

    @Override
    public Image getImage(TreePath2<TreeNode> path) {
        return null;
    }

    @Override
    public Weighter getWeighter() {
        return null;
    }

    @Override
    public Colorizer getColorizer() {
        return null;
    }

    @Override
    public void addChangeListener(ChangeListener l) {
    }

    @Override
    public void removeChangeListener(ChangeListener l) {
    }

    @Override
    public void toggleColorWeighter() {
        // do nothing
    }
    @Override
    public Action[] getActions(TreePath2<TreeNode> path) {
        return new Action[0];
    }
}
