/*
 * @(#)ManyEyesTree.java  1.1  2011-01-20
 * 
 * Copyright (c) 2009-2011 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.demo;

import ch.randelshofer.tree.NodeInfo;
import ch.randelshofer.tree.TreeNode;
import java.io.*;
import java.net.URL;
import java.util.*;
import java.util.regex.*;

/**
 * ManyEyesTree represents a tree structure in the tab-separated
 * table format used by
 * {@linkplain http://manyeyes.alphaworks.ibm.com/manyeyes/page/Data_Format.html Many Eyes}.
 *
 * @author Werner Randelshofer, Staldenmattweg 2, CH-6410 Goldau
 * @version 1.1 2011-01-20 Adds network support.
 * <br>1.0 2009-02-07 Created.
 */
public class ManyEyesTree implements DemoTree {

    private ManyEyesCompositeNode root;
    private String[] headers;
    private int[] pathIndices;
    private ArrayList<ManyEyesNode> nodes;
    private ManyEyesNodeInfo info;

    public ManyEyesTree(File manyEyesFile) throws IOException {
        FileInputStream in = new FileInputStream(manyEyesFile);
        try {
            read(in,manyEyesFile.getName());
        } finally {
            in.close();
        }
    }
    public ManyEyesTree(URL manyEyesFile) throws IOException {
        InputStream in = manyEyesFile.openStream();
        try {
            String name=manyEyesFile.getPath();
            int p=name.lastIndexOf('/');
            if (p!=-1) {
                name=name.substring(p+1);
            }

            read(in, name);
        } finally {
            in.close();
        }
    }

    public void read(InputStream in, String rootName) throws IOException {
        BufferedReader r = null;
        try {
            r = new BufferedReader(new InputStreamReader(in, "UTF-8"));
            Pattern pattern = Pattern.compile(" *\t *");

            // Read the header
            String line = r.readLine();
            headers = pattern.split(line);

            // Create the root node
            {
                String[] values = new String[headers.length];
                Arrays.fill(values, "");
                root = new ManyEyesCompositeNode(values);
                root.setName(rootName.substring(0, rootName.length() - 4));
            }

            // Create the nodes list
            nodes = new ArrayList<ManyEyesNode>();

            // Read the nodes
            while ((line = r.readLine()) != null) {
                String[] values = pattern.split(line);
                ManyEyesNode node = new ManyEyesNode(values);
                nodes.add(node);
            }

            // Create a default tree structure
            createDefaultTreeStructure();

        } finally {
            if (r != null) {
                r.close();
            }
        }
    }

    public String[] getHeaders() {
        return headers;
    }

    public int[] getPathIndices() {
        return pathIndices;
    }

    public ArrayList<ManyEyesNode> getNodes() {
        return nodes;
    }

    public void createDefaultTreeStructure() {
        int length = 1;
        for (; length < headers.length && headers[0].equals(headers[length]); length++) {
        }
        int[] indices = new int[length];
        for (int i = 0; i < length; i++) {
            indices[i] = i;
        }
        createTreeStructure(indices);
    }

    public void createTreeStructure(final int[] pathIndices) {
        this.pathIndices = pathIndices;

        // Sort nodes by path
        ArrayList<ManyEyesNode> sorted = (ArrayList<ManyEyesNode>) nodes.clone();
        Collections.sort(sorted, new Comparator<ManyEyesNode>() {

            public int compare(ManyEyesNode n1, ManyEyesNode n2) {
                String[] v1 = n1.getValues();
                String[] v2 = n2.getValues();
                for (int i = 0; i < pathIndices.length; i++) {
                    int c = v1[pathIndices[i]].compareTo(v2[pathIndices[i]]);
                    if (c != 0) {
                        return c;
                    }
                }
                return 0;
            }
        });


        root.removeAllChildren();
        ManyEyesCompositeNode parent = root;
        for (ManyEyesNode node : sorted) {
            // Find parent
            if (!isDescendantOf(node, parent) && parent != root) {
                ManyEyesNode child = (ManyEyesNode) parent.children().get(0);
                ManyEyesCompositeNode grandParent = parent.getParent();
                grandParent.remove(parent);
                grandParent.add(child);
                parent = grandParent;
            }
            while (!isDescendantOf(node, parent)) {
                parent = parent.getParent();
            }

            // Create artifical intermediate children, if necessary
            int parentDepth = getDepth(parent);
            int nodeDepth = getDepth(node);
            while (nodeDepth > parentDepth) {
                String[] artificial = new String[headers.length];
                Arrays.fill(artificial, "");
                String[] nv = node.getValues();
                for (int i = 0; i <= parentDepth; i++) {
                    artificial[pathIndices[i]] = nv[pathIndices[i]];
                }
                ManyEyesCompositeNode newParent = new ManyEyesCompositeNode(artificial);
                parent.add(newParent);
                newParent.setName(artificial[pathIndices[parentDepth]]);
                parent = newParent;
                parentDepth++;
            }


            node.setName(node.getValues()[pathIndices[nodeDepth - 1]]);

            // Add node to parent
            System.out.println("adding " + node + " to " + parent);
            parent.add(node);
        }
        if (parent != root) {
            // If the parent has only one child, remove unnecessary artifical parent
            ManyEyesNode child = (ManyEyesNode) parent.children().get(0);
            ManyEyesCompositeNode grandParent = parent.getParent();
            grandParent.remove(parent);
            grandParent.add(child);
        }
    }

    /**
     * Returns true if n1 is a descendant of n2.
     * @param n1
     * @param n2
     * @return
     */
    private boolean isDescendantOf(ManyEyesNode n1, ManyEyesNode n2) {
        // Short-circuit root, in case one of the nodes is a root as well
        if (n2 == root) {
            return true;
        }
        String[] v1 = n1.getValues();
        String[] v2 = n2.getValues();
        for (int i = 0; i < pathIndices.length && v2[pathIndices[i]].length() > 0; i++) {
            System.out.print("." + v1[pathIndices[i]]);
            if (!v1[pathIndices[i]].equals(v2[pathIndices[i]])) {
                System.out.println("#");
                return false;
            }
        }
        System.out.println();
        return true;
    }

    /**
     * Returns true if n1 is v1 descendant of n2.
     * @param v1
     * @param v2
     * @return
     */
    private int getDepth(ManyEyesNode n1) {
        int i = 0;
        String[] v1 = n1.getValues();
        for (; i < pathIndices.length && v1[pathIndices[i]].length() > 0 && !v1[pathIndices[i]].equals("-"); i++) {
        }
        return i;
    }

    public TreeNode getRoot() {
        return root;
    }

    public NodeInfo getInfo() {
        if (info == null) {
            info = new ManyEyesNodeInfo(this);
        }
        return info;
    }
}
