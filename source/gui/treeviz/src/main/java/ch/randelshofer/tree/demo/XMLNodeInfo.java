/*
 * @(#)XMLNodeInfo.java  1.0  23. Juni 2008
 *
 * Copyright (c) 2007 Werner Randelshofer, Goldau, Switzerland.
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
import ch.randelshofer.util.SizeFormat;
import ch.randelshofer.util.prefs.PreferencesUtil2;
import java.awt.Color;
import java.awt.Image;
import java.text.DecimalFormat;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.prefs.Preferences;
import javax.swing.Action;
import javax.swing.event.*;

/**
 * XMLNodeInfo produces information about generic XML files.
 * It attempts to interpret the XML attributes 'name', 'size', and 'created'
 * like file system attributes. 
 *
 * @author  Werner Randelshofer
 * @version 1.0 23. Juni 2008 Created.
 */
public class XMLNodeInfo extends AbstractNodeInfo {

    private SizeFormat shortWeightFormat;
    private SizeFormat longWeightFormat;
    private EventListenerList listenerList = new EventListenerList();
    private ChangeEvent changeEvent;
    private Colorizer colorizer;
    private Weighter colorWeighter;
    private Weighter weighter;
    private boolean isInitialized;
    private HashMap<String, HashSet<String>> attributes;
    private HashMap<String, DataType> types;
    private String nameAttribute;
    private String weightAttribute;
    private String colorAttribute;

    /** Creates a new instance. */
    public XMLNodeInfo() {
        colorizer = new RGBColorizer();
        //weighter = new LastModifiedWeighter();
        attributes = new HashMap<String, HashSet<String>>();

        shortWeightFormat = new SizeFormat();
        shortWeightFormat.setShortFormat(true);
        shortWeightFormat.setMaximumFractionDigits(0);
        longWeightFormat = new SizeFormat();
        longWeightFormat.setMaximumFractionDigits(1);
        longWeightFormat.setAlwaysIncludeBytes(true);
    }

    @Override
    public void init(TreeNode root) {
        init((XMLNode) root);
    }

    @Override
    public String getName(TreePath2<TreeNode> path) {
        XMLNode node = (XMLNode) path.getLastPathComponent();
        if (nameAttribute != null && node.getAttribute(nameAttribute) != null) {
            return node.getAttribute(nameAttribute);
        }
        return node.getName();
    }

    @Override
    public Color getColor(TreePath2<TreeNode> path) {
        XMLNode node = (XMLNode) path.getLastPathComponent();
        return (colorizer == null || colorWeighter == null) ? Color.WHITE : colorizer.get(colorWeighter.getWeight(path));
    }

    @Override
    public long getCumulatedWeight(TreePath2<TreeNode> path) {
        XMLNode node = (XMLNode) path.getLastPathComponent();
        return node.getCumulatedWeight();
        }
    @Override
    public long getWeight(TreePath2<TreeNode> path) {
        XMLNode node = (XMLNode) path.getLastPathComponent();
       
        if (weightAttribute != null && node.getAttribute(weightAttribute) != null) {
            return Math.max(1, Long.valueOf(node.getAttribute(weightAttribute)).longValue());
        }
        return node.getAllowsChildren() ? 0 : 1;
    }

    public Weighter getColorWeighter() {
        return colorWeighter;
    }
    /*
    public long getAccumulatedWeight(TreePath2<TreeNode> path) {
    XMLNode node = (XMLNode) path.getLastPathComponent();
    return node.getCumulatedWeight();
    }*/

    @Override
    public String getTooltip(TreePath2<TreeNode> path) {
        XMLNode node = (XMLNode) path.getLastPathComponent();

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

        buf.append("<br><b>weight: ");
        buf.append(formatSize(node.getCumulatedWeight()));
        buf.append("</b>");

        buf.append("<br>type: ");
        buf.append(node.getName());

        if (node.getAllowsChildren()) {
            buf.append("<br>children: ");
            buf.append(DecimalFormat.getIntegerInstance().format(node.children().size()));
        }

        Map<String, String> attr = node.getAttributes();
        for (Map.Entry<String, String> entry : attr.entrySet()) {
            buf.append("<br>" + entry.getKey() + ": ");
            if (entry.getKey().toLowerCase().endsWith("size") && types.get(entry.getKey()) == DataType.NUMERIC_STRING) {
                buf.append(formatSize(Long.valueOf(entry.getValue())));
            } else {
                buf.append(entry.getValue());

            }
        }

        return buf.toString();
    }

    private String formatSize(long w) {
        return longWeightFormat.format(w);
    }

    @Override
    public Image getImage(TreePath2<TreeNode> path) {
        XMLNode node = (XMLNode) path.getLastPathComponent();
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

    public void init(XMLNode root) {
        if (!isInitialized) {
            isInitialized = true;
            types = new HashMap<String, DataType>();
            attributes = new HashMap<String, HashSet<String>>();
            computeStats(root, types, attributes);
        }
    }

    public void computeStats(XMLNode root, HashMap<String, DataType> typeMap, HashMap<String, HashSet<String>> attrMap) {
        collectAttributesRecursively(root, attrMap);

        for (Map.Entry<String, HashSet<String>> entry : attrMap.entrySet()) {
            typeMap.put(entry.getKey(), determineDataType(entry.getValue()));
        }

        // Determine the name attribute
        Preferences prefs = PreferencesUtil2.userNodeForPackage(XMLFileAccessory.class);
        String rootElementName = root.getName();
        nameAttribute = prefs.get("xml." + rootElementName + ".nameAttribute", "<element>");
        weightAttribute = prefs.get("xml." + rootElementName + ".weightAttribute", "size");
        colorAttribute = prefs.get("xml." + rootElementName + ".colorAttribute", "created");


        if (nameAttribute.equals("<element>")) {
            nameAttribute = null; // No name
        } else if (typeMap.get(nameAttribute) != null) {
            // okay
        } else {
            for (Map.Entry<String, DataType> entry : typeMap.entrySet()) {
                if (entry.getValue() == DataType.TEXT_STRING) {
                    if (nameAttribute == null || nameAttribute.compareTo(entry.getKey()) > 0) {
                        nameAttribute = entry.getKey();
                    }
                }
            }
        }
        // Determine the weight attribute
        if (typeMap.get(weightAttribute) == DataType.NUMERIC_STRING) {
            // okay
        } else {
            for (Map.Entry<String, DataType> entry : typeMap.entrySet()) {
                if (entry.getValue() == DataType.NUMERIC_STRING) {
                    if (weightAttribute == null || weightAttribute.compareTo(entry.getKey()) > 0) {
                        weightAttribute = entry.getKey();
                    }
                }
            }
        }
        weighter = new XMLDateInfoWeighter(this, weightAttribute);
        root.accumulateWeights(this, null);

        // Determine the color attribute
        if (typeMap.get(colorAttribute) == DataType.DATE_STRING) {
            //okay
        } else if (typeMap.get(colorAttribute) == DataType.NUMERIC_STRING) {
            //okay
        } else if (typeMap.get(colorAttribute) == DataType.COLOR_STRING) {
            //okay
        } else {
            for (Map.Entry<String, DataType> entry : typeMap.entrySet()) {
                if (entry.getValue() == DataType.DATE_STRING) {
                    if (colorAttribute == null || colorAttribute.compareTo(entry.getKey()) > 0) {
                        colorAttribute = entry.getKey();
                    }
                }
            }
        }
        if (colorAttribute == null) {
            colorWeighter = null;
        } else {
            if (typeMap.get(colorAttribute) == DataType.DATE_STRING) {
                colorWeighter = new XMLDateInfoWeighter(this, colorAttribute);
            } else if (typeMap.get(colorAttribute) == DataType.NUMERIC_STRING) {
                colorWeighter = new XMLNumericInfoWeighter(this, colorAttribute);
            } else if (typeMap.get(colorAttribute) == DataType.TEXT_STRING) {
                colorWeighter = new XMLStringInfoWeighter(this, colorAttribute);
            } else if (typeMap.get(colorAttribute) == DataType.COLOR_STRING) {
                colorWeighter = new XMLColorStringInfoWeighter(this, colorAttribute);
            } else {
                colorWeighter = new XMLNumericInfoWeighter(this, colorAttribute);
            }
            colorWeighter.init(root);
        }
        if (colorWeighter != null) {
            if (colorWeighter instanceof XMLColorStringInfoWeighter) {
             colorizer=new ColorStringColorizer();   
            } else {
            colorizer = new RGBColorizer(new float[]{0f, colorWeighter.getMedianWeight(), 1f}, new Color[]{
                        new Color(0x64c8ff),
                        new Color(0xf5f5f5),
                        new Color(0xff9946)
                    });
            }
        }

    }

    public void collectAttributesRecursively(XMLNode node, HashMap<String, HashSet<String>> attrMap) {
        for (Map.Entry<String, String> entry : node.getAttributes().entrySet()) {
            String key = entry.getKey();
            String value = entry.getValue();
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
            collectAttributesRecursively((XMLNode) child, attrMap);
        }
    }

    public XMLNodeInfo.DataType getType(String key) {
        return types.get(key);
    }

    public Set<String> getValues(String key) {
        return attributes.get(key);
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
        return DecimalFormat.getIntegerInstance().format(getWeight(path));
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
