/**
 * @(#)TreePath2.java  1.0  Jan 26, 2008
 *
 * Copyright (c) 2008 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

package ch.randelshofer.tree;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.Vector;

/**
 * Reimplementation of javax.swing.TreePath2 with supports for generics.
 *
 * @author Werner Randelshofer
 * @version 1.0 Jan 26, 2008 Created.
 */
public class TreePath2<T> implements Serializable {
    /** Path representing the parent, null if lastPathComponent represents
     * the root. */
    private TreePath2<T>           parentPath;
    /** Last path component. */
    transient private T   lastPathComponent;

    /**
     * Constructs a path from an array of Objects, uniquely identifying 
     * the path from the root of the tree to a specific node, as returned
     * by the tree's data model.
     * <p>
     * The model is free to return an array of any Objects it needs to 
     * represent the path. The DefaultTreeModel returns an array of 
     * TreeNode objects. The first TreeNode in the path is the root of the
     * tree, the last TreeNode is the node identified by the path.
     *
     * @param path  an array of Objects representing the path to a node
     */
    public TreePath2(T[] path) {
        if(path == null || path.length == 0)
            throw new IllegalArgumentException("path in TreePath must be non null and not empty.");
	lastPathComponent = path[path.length - 1];
	if(path.length > 1)
	    parentPath = new TreePath2<T>(path, path.length - 1);
    }

    /**
     * Constructs a TreePath2 containing only a single element. This is
     * usually used to construct a TreePath2 for the the root of the TreeModel.
     * <p>
     * @param singlePath  an Object representing the path to a node
     * @see #TreePath2<T>(Object[])
     */
    public TreePath2(T singlePath) {
        if(singlePath == null)
            throw new IllegalArgumentException("path in TreePath must be non null.");
	lastPathComponent = singlePath;
	parentPath = null;
    }

    /**
     * Constructs a new TreePath2, which is the path identified by
     * <code>parent</code> ending in <code>lastElement</code>.
     */
    protected TreePath2(TreePath2<T> parent, T lastElement) {
	if(lastElement == null)
            throw new IllegalArgumentException("path in TreePath must be non null.");
	parentPath = parent;
	lastPathComponent = lastElement;
    }

    /**
     * Constructs a new TreePath2 with the identified path components of
     * length <code>length</code>.
     */
    protected TreePath2(T[] path, int length) {
	lastPathComponent = path[length - 1];
	if(length > 1)
	    parentPath = new TreePath2<T>(path, length - 1);
    }

    /**
     * Primarily provided for subclasses 
     * that represent paths in a different manner.
     * If a subclass uses this constructor, it should also override 
     * the <code>getPath</code>,
     * <code>getPathCount</code>, and
     * <code>getPathComponent</code> methods,
     * and possibly the <code>equals</code> method.
     */
    protected TreePath2() {
    }

    /**
     * Returns an ordered array of Objects containing the components of this
     * TreePath2. The first element (index 0) is the root.
     *
     * @return an array of Objects representing the TreePath2
     * @see #TreePath2<T>(Object[])
     */
    public T[] getPath() {
	int            i = getPathCount();
        T[]       result = (T[]) new Object[i--];

        for(TreePath2<T> path = this; path != null; path = path.parentPath) {
            result[i--] = path.lastPathComponent;
        }
	return result;
    }

    /**
     * Returns the last component of this path. For a path returned by
     * DefaultTreeModel this will return an instance of TreeNode.
     *
     * @return the Object at the end of the path
     * @see #TreePath2<T>(Object[])
     */
    public T getLastPathComponent() {
	return lastPathComponent;
    }

    /**
     * Returns the number of elements in the path.
     *
     * @return an int giving a count of items the path
     */
    public int getPathCount() {
        int        result = 0;
        for(TreePath2 path = this; path != null; path = path.parentPath) {
            result++;
        }
	return result;
    }

    /**
     * Returns the path component at the specified index.
     *
     * @param element  an int specifying an element in the path, where
     *                 0 is the first element in the path
     * @return the Object at that index location
     * @throws IllegalArgumentException if the index is beyond the length
     *         of the path
     * @see #TreePath2<T>(Object[])
     */
    public T getPathComponent(int element) {
        int          pathLength = getPathCount();

        if(element < 0 || element >= pathLength)
            throw new IllegalArgumentException("Index " + element + " is out of the specified range");

        TreePath2<T>         path = this;

        for(int i = pathLength-1; i != element; i--) {
           path = path.parentPath;
        }
	return path.lastPathComponent;
    }

    /**
     * Tests two TreePaths for equality by checking each element of the
     * paths for equality. Two paths are considered equal if they are of
     * the same length, and contain
     * the same elements (<code>.equals</code>).
     *
     * @param o the Object to compare
     */
    public boolean equals(Object o) {
	if(o == this)
	    return true;
        if(o instanceof TreePath2) {
            TreePath2<T>            oTreePath = (TreePath2<T>)o;

	    if(getPathCount() != oTreePath.getPathCount())
		return false;
	    for(TreePath2<T> path = this; path != null; path = path.parentPath) {
		if (!(path.lastPathComponent.equals
		      (oTreePath.lastPathComponent))) {
		    return false;
		}
		oTreePath = oTreePath.parentPath;
	    }
	    return true;
        }
        return false;
    }

    /**
     * Returns the hashCode for the object. The hash code of a TreePath2
     * is defined to be the hash code of the last component in the path.
     *
     * @return the hashCode for the object
     */
    public int hashCode() { 
	return lastPathComponent.hashCode();
    }

    /**
     * Returns true if <code>aTreePath</code> is a
     * descendant of this
     * TreePath2. A TreePath2 P1 is a descendent of a TreePath2 P2
     * if P1 contains all of the components that make up 
     * P2's path.
     * For example, if this object has the path [a, b],
     * and <code>aTreePath</code> has the path [a, b, c], 
     * then <code>aTreePath</code> is a descendant of this object.
     * However, if <code>aTreePath</code> has the path [a],
     * then it is not a descendant of this object.
     *
     * @return true if <code>aTreePath</code> is a descendant of this path
     */
    public boolean isDescendant(TreePath2 aTreePath) {
	if(aTreePath == this)
	    return true;

        if(aTreePath != null) {
            int                 pathLength = getPathCount();
	    int                 oPathLength = aTreePath.getPathCount();

	    if(oPathLength < pathLength)
		// Can't be a descendant, has fewer components in the path.
		return false;
	    while(oPathLength-- > pathLength)
		aTreePath = aTreePath.getParentPath();
	    return equals(aTreePath);
        }
        return false;
    }

    /**
     * Returns a new path containing all the elements of this object
     * plus <code>child</code>. <code>child</code> will be the last element
     * of the newly created TreePath2.
     * This will throw a NullPointerException
     * if child is null.
     */
    public TreePath2 pathByAddingChild(T child) {
	if(child == null)
	    throw new NullPointerException("Null child not allowed");

	return new TreePath2<T>(this, child);
    }

    /**
     * Returns a path containing all the elements of this object, except
     * the last path component.
     */
    public TreePath2 getParentPath() {
	return parentPath;
    }

    /**
     * Returns a string that displays and identifies this
     * object's properties.
     *
     * @return a String representation of this object
     */
    public String toString() {
        StringBuffer tempSpot = new StringBuffer("[");

        for(int counter = 0, maxCounter = getPathCount();counter < maxCounter;
	    counter++) {
            if(counter > 0)
                tempSpot.append(", ");
            tempSpot.append(getPathComponent(counter));
        }
        tempSpot.append("]");
        return tempSpot.toString();
    }

    // Serialization support.  
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();

        Vector      values = new Vector();
        boolean     writePath = true;

	if(lastPathComponent != null &&
	   (lastPathComponent instanceof Serializable)) {
            values.addElement("lastPathComponent");
            values.addElement(lastPathComponent);
        }
        s.writeObject(values);
    }

    private void readObject(ObjectInputStream s) 
        throws IOException, ClassNotFoundException {
        s.defaultReadObject();

        Vector          values = (Vector)s.readObject();
        int             indexCounter = 0;
        int             maxCounter = values.size();

        if(indexCounter < maxCounter && values.elementAt(indexCounter).
           equals("lastPathComponent")) {
            lastPathComponent = (T) values.elementAt(++indexCounter);
            indexCounter++;
        }
    }
}
