/*
 * @(#)FileNameComparator.java  1.0  September 16, 2007
 *
 * Copyright (c) 2007 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

package ch.randelshofer.tree.demo;

import ch.randelshofer.quaqua.filechooser.OSXCollator;
import java.io.File;
import java.text.Collator;
import java.util.Comparator;

/**
 * FileNameComparator.
 *
 * @author Werner Randelshofer
 * @version 1.0 September 16, 2007 Created.
 */
public class FileNameComparator implements Comparator {
    private static FileNameComparator instance;
    
    public static FileNameComparator getInstance() {
        if (instance == null) {
            instance = new FileNameComparator();
        }
        return instance;
    }
    
    /**
     * Compares two nodes using their collation keys.
     *
     * @param o1 An instance of AliasFileSystemTreeModel.Node.
     * @param o2 An instance of AliasFileSystemTreeModel.Node.
     */
    public int compare(Object o1, Object o2) {
        return OSXCollator.getInstance().compare(((File) o1).getName(), ((File) o2).getName());
    }
    
}
