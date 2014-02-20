/*
 * @(#)XMLNodeInfo.java  1.4  2011-08-11
 *
 * Copyright (c) 2007-2011 Werner Randelshofer, Goldau, Switzerland.
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
import ch.randelshofer.text.FileSizeFormat;
import ch.randelshofer.util.prefs.PreferencesUtil2;
import java.awt.Color;
import java.awt.Image;
import java.text.DecimalFormat;
import java.text.NumberFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.prefs.Preferences;
import javax.swing.Action;
import javax.swing.event.*;
import javax.swing.table.AbstractTableModel;
import javax.swing.table.TableModel;

/**
 * XMLNodeInfo produces information about generic XML files.
 * It attempts to interpret the XML attrMap 'name', 'size', and 'created'
 * like file system attrMap. 
 *
 * @author  Werner Randelshofer
 * @version 1.4 2011-08-11 Don't use preferences for  determining the weight,
 * color and name attribute.
 * <br>1.3 2011-01-20 Fall back to generic preferences.
 * <br>1.2 2010-10-17 Use preferences for determining the weight, color
 * and name attribute.
 * <br>1.1 2009-03-20 Factured weight formatting out.
 * <br>1.0.1 2009-03-04 Get cumulatedWeight if node has no fileSize attribute.
 * <br>1.0 23. Juni 2008 Created.
 */
public class TreevizFileSystemXMLNodeInfo extends AbstractNodeInfo {
    private FileSizeFormat shortWeightFormat;
    private FileSizeFormat longWeightFormat;
private TreevizFileSystemXMLNode root;
    private EventListenerList listenerList = new EventListenerList();
    private ChangeEvent changeEvent;
    private Colorizer colorizer;
    private Weighter colorWeighter;
    private Weighter weighter;
    private HashMap<String, TreevizFileSystemXMLNode> selectedUsers;
    private boolean isInitialized = false;

    private HashMap<String, HashSet<String>> attributes;
    private HashMap<String, DataType> types;
    private HashMap<String, HashSet<String>> userAttributes;
    private HashMap<String, TreevizFileSystemXMLNode> userMap;
    private HashMap<String, DataType> userTypes;
    private String nameAttribute;
    private String weightAttribute;
    private String colorAttribute;
    private TreevizFileSystemXMLTree tree;
    private static NumberFormat intFormat = DecimalFormat.getIntegerInstance();
    private static NumberFormat shortDecFormat;
    static {
        shortDecFormat = (NumberFormat) DecimalFormat.getNumberInstance().clone();
        shortDecFormat.setMaximumFractionDigits(1);
    }

    /** Creates a new instance. */
    public TreevizFileSystemXMLNodeInfo(TreevizFileSystemXMLTree tree) {
        colorizer = new RGBColorizer();
        //weighter = new LastModifiedWeighter();
        attributes = new HashMap<String, HashSet<String>>();
        this.tree = tree;
        shortWeightFormat =  new FileSizeFormat();
        shortWeightFormat.setShortFormat(true);
        shortWeightFormat.setMaximumFractionDigits(0);
        longWeightFormat =  new FileSizeFormat();
        longWeightFormat.setMaximumFractionDigits(1);
        longWeightFormat.setAlwaysIncludeBytes(true);
    }

    @Override
    public String getName(TreePath2<TreeNode> path) {
        TreevizFileSystemXMLNode node = (TreevizFileSystemXMLNode) path.getLastPathComponent();
        if (nameAttribute != null && node.getAttribute(nameAttribute) != null) {
            return node.getAttribute(nameAttribute).toString();
        }
        return node.getName();
    }

    @Override
    public Color getColor(TreePath2<TreeNode> path) {
        TreevizFileSystemXMLNode node = (TreevizFileSystemXMLNode) path.getLastPathComponent();
        return (!isNodeSelected(node) || colorizer == null || colorWeighter == null) ? Color.WHITE : colorizer.get(colorWeighter.getWeight(path));
    }
    @Override
    public long getCumulatedWeight(TreePath2<TreeNode> path) {
        return getWeight(path);
    }


    @Override
    public long getWeight(TreePath2<TreeNode> path) {
        TreevizFileSystemXMLNode node = (TreevizFileSystemXMLNode) path.getLastPathComponent();
        if (!node.getAllowsChildren() && weightAttribute != null && node.getAttribute(weightAttribute) != null) {
            return Math.max(1, Long.valueOf(node.getAttribute(weightAttribute).toString()).longValue());
        } else {
            return Math.max(0, node.getCumulatedWeight());
        }
    //return 1;
    }

    public long getAccumulatedWeight(TreePath2<TreeNode> path) {
        TreevizFileSystemXMLNode node = (TreevizFileSystemXMLNode) path.getLastPathComponent();
        return node.getCumulatedWeight();
    }

    @Override
    public String getTooltip(TreePath2<TreeNode> path) {
        TreevizFileSystemXMLNode node = (TreevizFileSystemXMLNode) path.getLastPathComponent();
        String ownerAttr = "ownerRef";
        TreevizFileSystemXMLNode userNode = userMap.get(node.getAttribute(ownerAttr));

        StringBuilder buf = new StringBuilder();
        TreePath2<TreeNode> parentPath = path;
        buf.insert(0, "</b><br>");
        buf.insert(0, getName(parentPath));
        buf.insert(0, "<b>");
        parentPath = parentPath.getParentPath();
        while (parentPath != null && parentPath.getPathCount() > 1) {
            buf.insert(0, "<br>");
            buf.insert(0, getName(parentPath));
            parentPath = parentPath.getParentPath();
        }
        buf.insert(0, "<html>");

        buf.append("<br>type: ").append(node.getName());
        buf.append("<br><b>size: ").append(longWeightFormat.format(node.getCumulatedWeight())).append("</b>");


        if (node.getAllowsChildren()) {
            buf.append("<br>children: ");
            buf.append(intFormat.format(node.children().size()));
            buf.append("<br>descendants: ");
            buf.append(intFormat.format(node.getDescendantCount()));
        }

        Map<String, Object> attr = node.getAttributes();
        TreeMap<String, Object> orderedMap = new TreeMap<String, Object>(attr);
        for (Map.Entry<String, Object> entry : orderedMap.entrySet()) {
            String key = entry.getKey();
            if (key.equals(ownerAttr)) {
                continue;
            }
            if (key.equals(nameAttribute)) {
                continue;
            }
            if (key.equals(weightAttribute)) {
                // skip - we printed the size already
                continue;
            }

            buf.append("<br>").append(key).append(": ");

            if (key.equals(weightAttribute) && types.get(key) == DataType.NUMERIC_STRING) {
                buf.append(longWeightFormat.format(Long.valueOf(entry.getValue().toString())));
            } else {
                buf.append(entry.getValue());

            }
        }

        buf.append("<br><br>owner: ");
        buf.append(node.getAttribute(ownerAttr));
        if (userNode != null) {
            attr = userNode.getAttributes();
            orderedMap = new TreeMap<String, Object>(attr);
            for (Map.Entry<String, Object> entry : orderedMap.entrySet()) {
                String key = entry.getKey();
                if (attr.containsKey("name") && (key.equals("firstname") || key.equals("lastname"))) {
                    // safe one line
                    continue;
                }
                if (key.equals("id")) {
                    // safe one line
                    continue;
                }
                buf.append("<br>" + key + ": ");
                if (key.equals("name")) {
                    buf.insert(buf.length()-key.length()-2,"<b>");
                    buf.append(entry.getValue());
                    buf.append(',');
                    if (attr.containsKey("firstname")) {
                        buf.append(' ');
                        buf.append(attr.get("firstname"));
                    }
                    if (attr.containsKey("lastname")) {
                        buf.append(' ');
                        buf.append(attr.get("lastname"));
                    }
                    buf.append("</b>");
                } else if (key.toLowerCase().endsWith("size") && userTypes.get(key) == DataType.NUMERIC_STRING) {
                    buf.append(longWeightFormat.format(Long.valueOf(entry.getValue().toString())));
                } else if (userTypes.get(key) == DataType.LONG) {
                    buf.append(longWeightFormat.format((Long) entry.getValue()));
                } else {
                    buf.append(entry.getValue());

                }
            }
        }
        return buf.toString();
    }

    @Override
    public Image getImage(TreePath2<TreeNode> path) {
        TreevizFileSystemXMLNode node = (TreevizFileSystemXMLNode) path.getLastPathComponent();
        return null;
    }

    @Override
    public Weighter getWeighter() {
        return colorWeighter;
    }

    @Override
    public Colorizer getColorizer() {
        return colorizer;
    }
    /*
    public void putAttribute(String key, String value) {
    HashSet<String> valueSet;
    if (attrMap.containsKey(key)) {
    valueSet = attrMap.get(key);
    } else {
    valueSet = new HashSet<String>();
    attrMap.put(key, valueSet);
    }
    valueSet.add(value);
    }*/

    @Override
    public void init(TreeNode root) {
        init((TreevizFileSystemXMLNode) root);
    }

    public void init(TreevizFileSystemXMLNode root) {
        this.root=root;
        if (!isInitialized) {
            isInitialized = true;
            userTypes = new HashMap<String, DataType>();
            userAttributes = new HashMap<String, HashSet<String>>();
            types = new HashMap<String, DataType>();
            attributes = new HashMap<String, HashSet<String>>();
            computeBasicStats(tree.getUsersRoot(), userTypes, userAttributes);
            computeBasicStats(root, types, attributes);
            computeFilesStats(root);
            computeUserStats(tree.getUsersRoot(), root);
        }
    }

    public void computeBasicStats(TreevizFileSystemXMLNode root, HashMap<String, DataType> typeMap, HashMap<String, HashSet<String>> attrMap) {
        collectAttributesRecursively(root, attrMap);
        for (Map.Entry<String, HashSet<String>> entry : attrMap.entrySet()) {
            typeMap.put(entry.getKey(), determineDataType(entry.getValue()));
        }

        // Determine the name attribute
        nameAttribute = null;
        if (typeMap.get("name") != null) {
            nameAttribute = "name";
        } else {
            for (Map.Entry<String, DataType> entry : typeMap.entrySet()) {
                if (entry.getValue() == DataType.TEXT_STRING) {
                    if (nameAttribute == null || nameAttribute.compareTo(entry.getKey()) > 0) {
                        nameAttribute = entry.getKey();
                    }
                }
            }
        }


    }

    public void computeFilesStats(TreevizFileSystemXMLNode root) {
        Preferences prefs = PreferencesUtil2.userNodeForPackage(XMLFileAccessory.class);
        String rootElementName = "TreevizFileSystem";
        
        // Use hardcoded value.
        /*
        nameAttribute = prefs.get("xml." + rootElementName + ".nameAttribute", prefs.get("xml.nameAttribute", "name"));
        weightAttribute = prefs.get("xml." + rootElementName + ".weightAttribute", prefs.get("xml.weightAttribute", "size"));
        colorAttribute = prefs.get("xml." + rootElementName + ".colorAttribute", prefs.get("xml.colorAttribute", "created"));
         */
        nameAttribute ="name";
        weightAttribute = "size";
        colorAttribute = "created";

        // Determine the weight attribute
        if (types.get(weightAttribute) != DataType.NUMERIC_STRING) {
            for (Map.Entry<String, DataType> entry : types.entrySet()) {
                if (entry.getValue() == DataType.NUMERIC_STRING) {
                    if (weightAttribute == null || weightAttribute.compareTo(entry.getKey()) > 0) {
                        weightAttribute = entry.getKey();
                    }
                }
            }
        }


        weighter = new TreevizFileSystemXMLInfoWeighter(this, weightAttribute);
        root.accumulateWeights(this, null);

        // Determine the color attribute
        if (types.get(colorAttribute) != DataType.DATE_STRING) {
            for (Map.Entry<String, DataType> entry : types.entrySet()) {
                if (entry.getValue() == DataType.DATE_STRING) {
                    if (colorAttribute == null || colorAttribute.compareTo(entry.getKey()) > 0) {
                        colorAttribute = entry.getKey();
                    }
                }
            }
        }
        if (colorAttribute == null) {
            weighter = null;
        } else {
            colorWeighter = new TreevizFileSystemXMLInfoWeighter(this, colorAttribute);
            colorWeighter.init(root);
        }
        colorizer = new RGBColorizer(new float[]{0f, ((TreevizFileSystemXMLInfoWeighter) colorWeighter).getMedianWeight(), 1f}, new Color[]{
                    new Color(0x64c8ff),
                    new Color(0xf0f0f0),
                    new Color(0xff9946)
                });

    }
    private void computeFilesStatsOld(TreevizFileSystemXMLNode root) {
        // Determine the weight attribute
        weightAttribute = null;
        if (types.get("size") == DataType.NUMERIC_STRING) {
            weightAttribute = "size";
        } else {
            for (Map.Entry<String, DataType> entry : types.entrySet()) {
                if (entry.getValue() == DataType.NUMERIC_STRING) {
                    if (weightAttribute == null || weightAttribute.compareTo(entry.getKey()) > 0) {
                        weightAttribute = entry.getKey();
                    }
                }
            }
        }


        weighter = new TreevizFileSystemXMLInfoWeighter(this, weightAttribute);
        root.accumulateWeights(this, null);

        // Determine the color attribute
        colorAttribute = null;

        if (types.get("created") == DataType.DATE_STRING) {
            colorAttribute = "created";
        } else {
            for (Map.Entry<String, DataType> entry : types.entrySet()) {
                if (entry.getValue() == DataType.DATE_STRING) {
                    if (colorAttribute == null || colorAttribute.compareTo(entry.getKey()) > 0) {
                        colorAttribute = entry.getKey();
                    }
                }
            }
        }
        if (colorAttribute == null) {
            weighter = null;
        } else {
            colorWeighter = new TreevizFileSystemXMLInfoWeighter(this, colorAttribute);
            colorWeighter.init(root);
        }
        colorizer = new RGBColorizer(new float[]{0f, ((TreevizFileSystemXMLInfoWeighter) colorWeighter).getMedianWeight(), 1f}, new Color[]{
                    new Color(0x64c8ff),
                    new Color(0xf0f0f0),
                    new Color(0xff9946)
                });

    }

    public void collectAttributesRecursively(TreevizFileSystemXMLNode node, HashMap<String, HashSet<String>> attrMap) {
        for (Map.Entry<String, Object> entry : node.getAttributes().entrySet()) {
            String key = entry.getKey();
            Object obj = entry.getValue();
            String value = (obj != null) ? obj.toString() : null;
            HashSet<String> valueSet;
            if (attrMap.containsKey(key)) {
                valueSet = attrMap.get(key);
            } else {
                valueSet = new HashSet<String>();
                attrMap.put(key, valueSet);
            }
            valueSet.add(value);
        }
        for (TreeNode child : node.children()) {
            collectAttributesRecursively((TreevizFileSystemXMLNode) child, attrMap);
        }
    }

    public void computeUserStats(TreevizFileSystemXMLNode usersRoot, TreevizFileSystemXMLNode filesRoot) {
        userMap = new HashMap<String, TreevizFileSystemXMLNode>();

        String idAttr = "id";
        for (TreeNode child : usersRoot.children()) {
            TreevizFileSystemXMLNode userNode = (TreevizFileSystemXMLNode) child;
            if (userNode.getAttribute(idAttr) != null) {
                userMap.put(userNode.getAttribute(idAttr).toString(), userNode);
            }
            userNode.putAttribute("disk usage", null);
            userNode.putAttribute("owned objects", null);
        }
        userTypes.put("disk usage", DataType.LONG);
        userTypes.put("owned objects", DataType.INTEGER);
        computeUserFileStatsRecursive(filesRoot);
    }

    public void computeUserFileStatsRecursive(TreevizFileSystemXMLNode filesNode) {
        if (filesNode.getAttribute("ownerRef") != null) {
            TreevizFileSystemXMLNode userNode = userMap.get(filesNode.getAttribute("ownerRef"));
            if (userNode != null) {
                if (filesNode.children().size() == 0) {
                    Long weight = (Long) userNode.getAttribute("disk usage");
                    userNode.putAttribute("disk usage", (weight == null) ? 1L : weight + filesNode.getCumulatedWeight());
                    userNode.setCumulatedWeight(userNode.getCumulatedWeight() + filesNode.getCumulatedWeight());
                }
                Integer count = (Integer) userNode.getAttribute("owned objects");
                userNode.putAttribute("owned objects", (count == null) ? 1 : count + 1);
            }
        }

        for (TreeNode child : filesNode.children()) {
            computeUserFileStatsRecursive((TreevizFileSystemXMLNode) child);
        }
    }

    public TreevizFileSystemXMLNodeInfo.DataType getType(String key) {
        return types.get(key);
    }

    public Set<String> getValues(String key) {
        return attributes.get(key);
    }

    public boolean isNodeSelected(TreevizFileSystemXMLNode node) {
        if (selectedUsers == null || selectedUsers.isEmpty()) {
            return true;
        } else {
            Object ref = node.getAttribute("ownerRef");
            return selectedUsers.containsKey(ref);
        }
    }

    public void setSelectedUsers(HashMap<String, TreevizFileSystemXMLNode> newValue) {
        this.selectedUsers = newValue;
        fireStateChanged();
    }

    public TableModel getUserTable() {
        final ArrayList<TreevizFileSystemXMLNode> rows = new ArrayList<TreevizFileSystemXMLNode>();
        rows.addAll(userMap.values());
        Collections.sort(rows, new Comparator<TreevizFileSystemXMLNode>() {

            @Override
            public int compare(TreevizFileSystemXMLNode o1, TreevizFileSystemXMLNode o2) {
                long diff = o2.getCumulatedWeight() - o1.getCumulatedWeight();
                if (diff > 0) {
                    return 1;
                } else if (diff < 0) {
                    return -1;
                } else {
                    return 0;
                }
            }
        });

        ArrayList<String> columns = new ArrayList<String>();
        columns.addAll(userTypes.keySet());
        Collections.sort(columns);
        String[] preferredOrder = {"id", "name", "firstname", "lastname", "email", "matriculation", "created", "expired", "isActive", "used"};
        for (int i = preferredOrder.length - 1; i >= 0; i--) {
            if (columns.contains(preferredOrder[i])) {
                columns.remove(preferredOrder[i]);
                columns.add(0, preferredOrder[i]);
            }
        }
        return new InfoTableModel(rows, columns);
    }

    @Override
    public void toggleColorWeighter() {
        if (colorWeighter instanceof TreevizFileSystemXMLByYearInfoWeighter) {
            colorWeighter = new TreevizFileSystemXMLInfoWeighter(this, colorAttribute);
            colorWeighter.init(root);
        colorizer = new RGBColorizer(new float[]{0f, ((TreevizFileSystemXMLInfoWeighter) colorWeighter).getMedianWeight(), 1f}, new Color[]{
                    new Color(0x64c8ff),
                    new Color(0xf0f0f0),
                    new Color(0xff9946)
                });
        } else {
            colorWeighter = new TreevizFileSystemXMLByYearInfoWeighter(this, colorAttribute, "size");
            colorWeighter.init(root);
//            colorizer = new HSBColorizer(new float[]{ 0.5f, 0.5f, 1f},//
//                  new float[]{0f, 0.5f, 1f});
        colorizer = new RGBColorizer(new float[]{0f, 1f}, new Color[]{
                        new Color(0x346eb6),
                    new Color(0xf0f0f0)});

        }
    }

    public class InfoTableModel extends AbstractTableModel {

        private ArrayList<TreevizFileSystemXMLNode> rows;
        private ArrayList<String> columns = new ArrayList<String>();

        public InfoTableModel(ArrayList<TreevizFileSystemXMLNode> rows, ArrayList<String> columns) {
            this.rows = rows;
            this.columns = columns;
        }

        @Override
        public int getRowCount() {
            return rows.size();
        }

        @Override
        public String getColumnName(int column) {
            return columns.get(column);
        }

        @Override
        public Class<?> getColumnClass(int columnIndex) {
            switch (userTypes.get(columns.get(columnIndex))) {
                case LONG:
                    return Long.class;
                case INTEGER:
                    return Integer.class;
                default:
                    return String.class;
            }
        /*
        return Long.class;
        } else if (userTypes.get(columns.get(columnIndex)) == DataType.LONG) {
        return Long.class;
        } else {
        return String.class; // FIXME 
        }*/
        }

        @Override
        public int getColumnCount() {
            return columns.size();
        }

        @Override
        public Object getValueAt(int rowIndex, int columnIndex) {
            return rows.get(rowIndex).getAttribute(columns.get(columnIndex));
        }

        public TreevizFileSystemXMLNode getRowObject(int row) {
            return rows.get(row);
        }
    }

    @Override
    public void addChangeListener(ChangeListener l) {
        listenerList.add(ChangeListener.class, l);
    }

    /** Removes a change listener from the button. */
    @Override
    public void removeChangeListener(ChangeListener l) {
        listenerList.remove(ChangeListener.class, l);
    }
    /*
     * Notify all listeners that have registered interest for
     * notification on this event type.  The event instance
     * is lazily created using the parameters passed into
     * the fire method.
     *
     * @see EventListenerList
     */

    protected void fireStateChanged() {
        // Guaranteed to return a non-null array
        Object[] listeners = listenerList.getListenerList();
        // Process the listeners last to first, notifying
        // those that are interested in this event
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ChangeListener.class) {
                // Lazily create the event:
                if (changeEvent == null) {
                    changeEvent = new ChangeEvent(this);
                }
                ((ChangeListener) listeners[i + 1]).stateChanged(changeEvent);
            }
        }
    }

    @Override
    public String getWeightFormatted(TreePath2<TreeNode> path) {
        return shortWeightFormat.format(getWeight(path));
    }

    @Override
    public Action[] getActions(TreePath2<TreeNode> path) {
        return new Action[0];
    }
}
