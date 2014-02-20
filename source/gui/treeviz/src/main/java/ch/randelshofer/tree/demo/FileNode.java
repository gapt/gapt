/*
 * @(#)FileNode.java  1.0  September 16, 2007
 *
 * Copyright (c) 2007 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.demo;

import ch.randelshofer.gui.*;
import ch.randelshofer.tree.*;
import java.awt.Color;
import java.io.File;
import java.util.*;

/**
 * The FileNode implements an example of HTNode encapsulating a File.
 */
public class FileNode
        implements TreeNode {

    private File file = null; // the File encapsulated
    private ArrayList<TreeNode> children = null; // the children of this node
    private int depth;
    private boolean isLeaf;
    private long fileSize = -1;
    private int size = -1;
    private long lastModified;
    private int descendants = -1;
    /* --- Constructor --- */

    /**
     * Constructor.
     *
     * @param file    the File encapsulated in this node
     */
    public FileNode(File file) {
        this(null, 0, file);

    }

    public FileNode(File file, File onlyChild) {
        this(null, 0, file, onlyChild);

    }

    /**
     * Constructor.
     *
     * @param file    the File encapsulated in this node
     */
    public FileNode(ProgressObserver p, int depth, File file) {
        this(p, depth, file, null);
    }

    /**
     * Constructor.
     *
     * @param file    the File encapsulated in this node
     */
    public FileNode(ProgressObserver p, int depth, File file, File onlyChild) {
        ProgressObserver oldP = p;
        if (p == null) {
            p = new ProgressView("Opening " + file.getName(), "", 0, 1);
            p.setIndeterminate(true);
        }
        this.depth = depth;
        this.lastModified = file.lastModified();
        boolean isDir = file.isDirectory();
        this.isLeaf = !isDir;
        this.file = file;
        children = new ArrayList();
        if (isLeaf || p.isCanceled()) {
            fileSize = file.length();
        } else {
            p.setNote("Reading (" + p.getProgress() + ") " + file.getName());
            File[] tabFichiers = (onlyChild == null) ? file.listFiles() : new File[]{onlyChild};
            fileSize = 0;
            if (tabFichiers != null) {
                p.setMaximum(p.getMaximum() + tabFichiers.length);
                for (int i = 0, n = tabFichiers.length; i < n; i++) {
                    File fichier = tabFichiers[i];
                    if (!fichier.isHidden()) {
                        FileNode child = new FileNode(p, depth + 1, fichier);
                        fileSize += child.getFileSize();
                        addChild(child);
                    }
                }
            }
        }
        size = (fileSize == 0) ? 0 : Math.max(0, Math.min(10, (int) Math.log10(fileSize) - 5));
        p.setProgress(p.getProgress() + 1);
        if (oldP == null) {
            p.close();
        }
    }

    public long getLastModified() {
        return lastModified;
    }

    /* --- Tree management --- */
    /**
     * Add child to the node.
     * 
     * @param child    the HSBFileNodeto add as a child
     */
    protected void addChild(FileNode child) {
        children.add(child);
    }

    /* --- HTNode --- */
    /**
     * Returns the children of this node in an Enumeration.
     * If this node is a file, return a empty Enumeration.
     * Else, return an Enumeration full with FileNode.
     * 
     * 
     * @return an Iterator containing child values of this node
     */
    @Override
    public List<TreeNode> children() {
        return (List<TreeNode>) children;
    }

    /**
     * Returns true if this node is not a directory.
     *
     * @return    <CODE>false</CODE> if this node is a directory;
     *            <CODE>true</CODE> otherwise
     */
    @Override
    public boolean getAllowsChildren() {
        return !isLeaf;
    }

    /**
     * Returns the name of the file.
     *
     * @return    the name of the file
     */
    public String getName() {
        return file.getName();
    }

    public long getFileSize() {
        return fileSize;
    }

    public long getUnweightedSize() {
        return fileSize;
    }

    public float getWeight() {
        return (float) Math.min(1, Math.max(0, Math.log10(fileSize / (double) (10 * 1024 * 1024))));
    }

    public File getFile() {
        return file;
    }



    public String getToolTipText() {
        long len = getFileSize();
        String unit = "bytes";
        if (len > 1024) {
            len /= 1024;
            unit = "KB";
            if (len > 1024) {
                len /= 1024;
                unit = "MB";
                if (len > 1024) {
                    len /= 1024;
                    unit = "GB";
                }
            }
        }
        StringBuffer buf = new StringBuffer();
        buf.append("<html>");
        buf.append(getName());
        if (file.isDirectory()) {
            buf.append("<br>");
            buf.append(children.size());
            buf.append(" files");
        }
        buf.append("<br>");
        buf.append(len);
        buf.append(' ');
        buf.append(unit);
        buf.append("<br>");
        buf.append(new Date(file.lastModified()));
        return buf.toString();
    }

    public void dump(int depth) {
        System.out.println(depth + " " + getName());
        for (TreeNode c : children()) {
            FileNode child = (FileNode) c;
            child.dump(depth + 1);
        }
    }

    public int getDescendantCount() {
        if (descendants == -1) {
            descendants = 0;
            if (children != null) {
                descendants += children.size();
                for (TreeNode child : children) {
                    descendants += ((FileNode) child).getDescendantCount();
                }
            }
        }
        return descendants;
    }

    @Override
    public String toString() {
        return "FileNode[" + getName() + "]";
    }
}

