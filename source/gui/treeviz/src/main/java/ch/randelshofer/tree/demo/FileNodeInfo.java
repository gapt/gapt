/*
 * @(#)FileNodeInfo.java  1.2  2011-01-16
 *
 * Copyright (colorizer) 2007-2011 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.demo;

import ch.randelshofer.tree.*;
import ch.randelshofer.tree.Colorizer;
import ch.randelshofer.tree.Weighter;
import ch.randelshofer.text.FileSizeFormat;
import java.awt.Color;
import java.awt.Desktop;
import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.text.DateFormat;
import java.text.DecimalFormat;
import java.text.NumberFormat;
import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.plaf.basic.BasicToolTipUI;

/**
 * FileNodeInfo.
 * 
 * @author Werner Randelshofer
 * @version 1.2 2011-01-16 Added actions for opening files and folders.
 * <br>1.1 2009-03-20 Factured weight formatting out.
 * <br>1.0 September 25, 2007 Created.
 */
public class FileNodeInfo extends DefaultNodeInfo {

    private FileSizeFormat shortWeightFormat;
    private FileSizeFormat longWeightFormat;
    private Colorizer colorizer;
    private Weighter weighter;
    private Weighter colorWeighter;
    private int colorWeighterToggle;
    private static FileSizeFormat byteFormat;
    private TreeNode root;

    static {
        byteFormat = new FileSizeFormat();
        byteFormat.setShortFormat(false);
        byteFormat.setMaximumFractionDigits(1);
    }
    private static NumberFormat intFormat = DecimalFormat.getIntegerInstance();

    /** Creates a new instance. */
    public FileNodeInfo() {
        colorizer = new RGBColorizer();
        colorWeighter = weighter = new LastModifiedWeighter();
        shortWeightFormat = new FileSizeFormat();
        shortWeightFormat.setShortFormat(true);
        shortWeightFormat.setMaximumFractionDigits(0);
        longWeightFormat = new FileSizeFormat();
        longWeightFormat.setMaximumFractionDigits(1);
        longWeightFormat.setAlwaysIncludeBytes(true);
    }

    @Override
    public void init(TreeNode root) {
        this.root = root;
        toggleColorWeighter();

        BasicToolTipUI tt;
    }

    @Override
    public Weighter getWeighter() {
        return colorWeighter;
    }

    @Override
    public Colorizer getColorizer() {
        return colorizer;
    }

    @Override
    public long getWeight(TreePath2<TreeNode> path) {
        FileNode fn = (FileNode) path.getLastPathComponent();
        return fn.getFileSize();
    }

    @Override
    public Color getColor(TreePath2<TreeNode> path) {
        FileNode fn = (FileNode) path.getLastPathComponent();
        return colorizer.get(weighter.getWeight(path));
    }

    @Override
    public String getName(TreePath2<TreeNode> path) {
        FileNode fn = (FileNode) path.getLastPathComponent();
        return fn.getName();
    }

    @Override
    public String getTooltip(TreePath2<TreeNode> path) {
        StringBuilder buf = new StringBuilder();

        TreePath2<TreeNode> parentPath = path;
        do {
            buf.insert(0, "<br>");
            buf.insert(0, getName(parentPath));
            parentPath = parentPath.getParentPath();
        } while (parentPath != null);
        buf.insert(0, "<html>");
        buf.append("<br>");

        FileNode node = (FileNode) path.getLastPathComponent();
        if (node.getAllowsChildren()) {
            buf.append("<br>children: ");
            buf.append(intFormat.format(node.children().size()));
            buf.append("<br>descendants: ");
            buf.append(intFormat.format(node.getDescendantCount()));
        }

        buf.append("<br>size: ");
        buf.append(longWeightFormat.format(getWeight(path)));

        buf.append("<br>last modified: ");
        buf.append(DateFormat.getDateTimeInstance().format(node.getLastModified()));

        return buf.toString();
    }

    @Override
    public String getWeightFormatted(TreePath2<TreeNode> path) {
        return shortWeightFormat.format(getWeight(path));
    }

    @Override
    public void toggleColorWeighter() {
        colorWeighterToggle=(colorWeighterToggle+1)%4;
        
        switch (colorWeighterToggle) {
            case 0:
            default:
            colorWeighter = new LastModifiedWeighter();
            colorWeighter.init(root);
            colorizer = new RGBColorizer(new float[]{0f, ((LastModifiedWeighter) colorWeighter).getMedianWeight(), 1f}, //
                    new Color[]{
                        new Color(0x64c8ff),
                        new Color(0xf5f5f5),
                        new Color(0xff9946)
                    });
                break;
            case 1:
            colorWeighter = new LastModifiedByYearWeighter();
            colorWeighter.init(root);
//            colorizer = new HSBColorizer(new float[]{ 0f, 0.5f, 1f},//
//                  new float[]{0.5f, 0.5f, 1f});
            colorizer = new RGBColorizer(new float[]{0f, 1f}, new Color[]{
                        new Color(0x346eb6),
                        new Color(0xf0f0f0)});
                break;
            case 2:
            colorWeighter = new LastModifiedWeighter();
            colorWeighter.init(root);
            colorizer = new HSBColorizer(new float[]{ 0f, 0.5f, 1f},//
                  new float[]{0.5f, 0.5f, 1f});
                break;
            case 3:
            colorWeighter = new LastModifiedWeighter();
            colorWeighter.init(root);
            colorizer = new HSBColorizer(new float[]{ 0f, 0.4f, 0.7f},//
                  new float[]{0.9f, 0.4f, 0.7f});
                break;
        }
    }

    @Override
    public Action[] getActions(TreePath2<TreeNode> path) {
        FileNode n = (FileNode) path.getLastPathComponent();
        final File file = n.getFile();
        if (file.isDirectory()) {
            Action a = new AbstractAction("Open Folder") {

                @Override
                public void actionPerformed(ActionEvent e) {
                    try {
                        Desktop.getDesktop().open(file);
                    } catch (IOException ex) {
                        ex.printStackTrace();
                    }
                }
            };
            return new Action[]{a};
        } else {
            Action a1 = new AbstractAction("Open Parent Folder") {

                @Override
                public void actionPerformed(ActionEvent e) {
                    try {
                        Desktop.getDesktop().open(file.getParentFile());
                    } catch (IOException ex) {
                        ex.printStackTrace();
                    }
                }
            };
            Action a2 = new AbstractAction("Open File") {

                @Override
                public void actionPerformed(ActionEvent e) {
                    try {
                        Desktop.getDesktop().open(file);
                    } catch (IOException ex) {
                        ex.printStackTrace();
                    }
                }
            };
            return new Action[]{a1,a2};
        }
    }
}
