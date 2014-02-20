/*
 * @(#)XMLFileAccessory.java  1.1  2011-08-11
 * 
 * Copyright (c) 2010 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms..
 */
package ch.randelshofer.tree.demo;

import ch.randelshofer.util.Worker;
import ch.randelshofer.util.prefs.PreferencesUtil2;
import java.awt.Component;
import java.awt.Font;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.File;
import java.util.TreeSet;
import java.util.prefs.Preferences;
import javax.swing.DefaultComboBoxModel;
import javax.swing.JComponent;
import javax.swing.JFileChooser;
import javax.xml.parsers.SAXParser;
import javax.xml.parsers.SAXParserFactory;
import org.xml.sax.Attributes;
import org.xml.sax.SAXException;
import org.xml.sax.ext.DefaultHandler2;

/**
 * XMLFileAccessory can be used with a filechooser or as a standalone
 * panel to specify the attribute which shall be used for coloring and for
 * sizing a tree node.
 *
 * @author Werner Randelshofer
 * @version 1.1 2011-08-11 Hide choices when TreevizFileSystem is detected.
 * <br>1.0 2010-08-19 Created.
 */
public class XMLFileAccessory extends javax.swing.JPanel {

    private File file;
    private JFileChooser fileChooser;
    private Preferences prefs;

    /** Creates new form XMLFileAccessory */
    private class Handler implements PropertyChangeListener {

        @Override
        public void propertyChange(PropertyChangeEvent evt) {
            String n = evt.getPropertyName();
            if (n == JFileChooser.SELECTED_FILE_CHANGED_PROPERTY) {
                updateFile((File) evt.getNewValue());
            }
        }
    }
    private Handler handler = new Handler();

    public XMLFileAccessory() {
        initComponents();
        prefs = PreferencesUtil2.userNodeForPackage(XMLFileAccessory.class);

        Font smallSystemFont = new Font("Dialog", Font.PLAIN, 11);
        for (Component c : getComponents()) {
            JComponent jc = (JComponent) c;
            jc.setFont(smallSystemFont);
            jc.putClientProperty("JComponent.sizeVariant", "small");
        }
    }

    public void setFileChooser(JFileChooser fc) {
        if (fileChooser != null) {
            fileChooser.removePropertyChangeListener(handler);
        }
        fileChooser = fc;
        if (fileChooser != null) {
            fileChooser.addPropertyChangeListener(handler);
        }
    }

    private void updateFile(final File f) {
        rootElementField.setText("");
        nameAttributeField.setModel(new DefaultComboBoxModel());
        colorAttributeField.setModel(new DefaultComboBoxModel());
        weightAttributeField.setModel(new DefaultComboBoxModel());
        rootElementField.setEnabled(false);
        nameAttributeField.setEnabled(false);
        colorAttributeField.setEnabled(false);
        weightAttributeField.setEnabled(false);
        file = null;
        if (f == null) {
            return;
        }
        new Worker<TreeSet<String>>() {

            private String rootElementName;

            @Override
            protected TreeSet<String> construct() throws Exception {
                final TreeSet<String> attrNames = new TreeSet();
                SAXParserFactory factory = SAXParserFactory.newInstance();
                SAXParser saxParser = factory.newSAXParser();

                try {
                    saxParser.parse(f, new DefaultHandler2() {

                        private int count;

                        @Override
                        public void startElement(String uri, String localName, String qName, Attributes attributes) throws SAXException {
                            if (rootElementName == null) {
                                rootElementName = qName;
                            } else {
                                for (int i = 0, n = attributes.getLength(); i < n; i++) {
                                    attrNames.add(attributes.getQName(i));
                                }
                            }
                            if (++count > 100) {
                                throw new SAXException("done");
                            }

                        }
                    });
                } catch (SAXException e) {
                    if (e.getMessage() != "done") {
                        throw e;
                    }
                }
                return attrNames;
            }

            @Override
            protected void done(TreeSet<String> attrSet) {
                rootElementField.setEnabled(true);
                rootElementField.setText(rootElementName);

                if (rootElementName.equals("TreevizFileSystem")) {
                    // Use hardcoded value for TreevizFileSystem!
                    nameAttributeField.setModel(new DefaultComboBoxModel(new String[]{"name"}));
                    colorAttributeField.setModel(new DefaultComboBoxModel(new String[]{"created"}));
                    weightAttributeField.setModel(new DefaultComboBoxModel(new String[]{"size"}));
                    colorAttributeField.setEnabled(false);
                    weightAttributeField.setEnabled(false);
                    nameAttributeField.setEnabled(false);
                    return;
                }

                if (attrSet.size() > 0) {
                    nameAttributeField.setEnabled(true);
                    TreeSet<String> nameAttrSet = new TreeSet<String>();
                    nameAttrSet.add("<element>");
                    nameAttrSet.addAll(attrSet);
                    nameAttributeField.setModel(new DefaultComboBoxModel(nameAttrSet.toArray()));
                    colorAttributeField.setEnabled(true);
                    weightAttributeField.setEnabled(true);
                    colorAttributeField.setModel(new DefaultComboBoxModel(attrSet.toArray()));
                    weightAttributeField.setModel(new DefaultComboBoxModel(attrSet.toArray()));

                    String nameAttr = prefs.get("xml." + rootElementName + ".nameAttribute", "<element>");
                    String weightAttr = prefs.get("xml." + rootElementName + ".weightAttribute", "size");
                    String colorAttr = prefs.get("xml." + rootElementName + ".colorAttribute", "created");
                    if (nameAttrSet.contains(nameAttr)) {
                        nameAttributeField.setSelectedItem(nameAttr);
                    } else {
                        nameAttributeField.setSelectedItem(nameAttrSet.first());
                        prefs.put("xml." + rootElementName + ".nameAttribute", nameAttrSet.first());

                    }
                    if (attrSet.contains(weightAttr)) {
                        weightAttributeField.setSelectedItem(weightAttr);
                    } else {
                        weightAttributeField.setSelectedItem(attrSet.first());
                        prefs.put("xml." + rootElementName + ".weightAttribute", attrSet.first());

                    }
                    if (attrSet.contains(colorAttr)) {
                        colorAttributeField.setSelectedItem(colorAttr);
                    } else {
                        colorAttributeField.setSelectedItem(attrSet.last());
                        prefs.put("xml." + rootElementName + ".colorAttribute", attrSet.last());
                    }
                }
            }

            @Override
            protected void failed(Throwable error) {
                error.printStackTrace();
                // nothing to do, since we already disabled the fields
            }
        }.start();
    }

    private String getRootElementName() {
        return rootElementField.getText() == null ? "" : rootElementField.getText();
    }

    /** This method is called from within the constructor to
     * initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is
     * always regenerated by the Form Editor.
     */
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {
        java.awt.GridBagConstraints gridBagConstraints;

        rootElementLabel = new javax.swing.JLabel();
        rootElementField = new javax.swing.JTextField();
        nameAttributeLabel = new javax.swing.JLabel();
        nameAttributeField = new javax.swing.JComboBox();
        weightAttributeLabel = new javax.swing.JLabel();
        weightAttributeField = new javax.swing.JComboBox();
        colorAttributeLabel = new javax.swing.JLabel();
        colorAttributeField = new javax.swing.JComboBox();

        FormListener formListener = new FormListener();

        setBorder(javax.swing.BorderFactory.createEmptyBorder(8, 8, 8, 8));
        setLayout(new java.awt.GridBagLayout());

        rootElementLabel.setText("Root Element:");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.NORTHWEST;
        add(rootElementLabel, gridBagConstraints);

        rootElementField.setColumns(12);
        rootElementField.setEditable(false);
        rootElementField.setBorder(javax.swing.BorderFactory.createEmptyBorder(1, 1, 1, 1));
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.fill = java.awt.GridBagConstraints.HORIZONTAL;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.NORTHWEST;
        add(rootElementField, gridBagConstraints);

        nameAttributeLabel.setText("Name Attribute:");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.NORTHWEST;
        gridBagConstraints.insets = new java.awt.Insets(8, 0, 0, 0);
        add(nameAttributeLabel, gridBagConstraints);

        nameAttributeField.addActionListener(formListener);
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.fill = java.awt.GridBagConstraints.HORIZONTAL;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.NORTHWEST;
        add(nameAttributeField, gridBagConstraints);

        weightAttributeLabel.setText("Weight Attribute:");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.NORTHWEST;
        gridBagConstraints.insets = new java.awt.Insets(8, 0, 0, 0);
        add(weightAttributeLabel, gridBagConstraints);

        weightAttributeField.addActionListener(formListener);
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.fill = java.awt.GridBagConstraints.HORIZONTAL;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.NORTHWEST;
        add(weightAttributeField, gridBagConstraints);

        colorAttributeLabel.setText("Color Attribute:");
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.NORTHWEST;
        gridBagConstraints.insets = new java.awt.Insets(8, 0, 0, 0);
        add(colorAttributeLabel, gridBagConstraints);

        colorAttributeField.addActionListener(formListener);
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.fill = java.awt.GridBagConstraints.HORIZONTAL;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.NORTHWEST;
        gridBagConstraints.weightx = 1.0;
        gridBagConstraints.weighty = 1.0;
        add(colorAttributeField, gridBagConstraints);
    }

    // Code for dispatching events from components to event handlers.

    private class FormListener implements java.awt.event.ActionListener {
        FormListener() {}
        public void actionPerformed(java.awt.event.ActionEvent evt) {
            if (evt.getSource() == weightAttributeField) {
                XMLFileAccessory.this.sizeFieldPerformed(evt);
            }
            else if (evt.getSource() == colorAttributeField) {
                XMLFileAccessory.this.colorFieldPerformed(evt);
            }
            else if (evt.getSource() == nameAttributeField) {
                XMLFileAccessory.this.nameFieldPerformed(evt);
            }
        }
    }// </editor-fold>//GEN-END:initComponents

    private void sizeFieldPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_sizeFieldPerformed
        prefs.put("xml." + getRootElementName() + ".weightAttribute", (String) weightAttributeField.getSelectedItem());
    }//GEN-LAST:event_sizeFieldPerformed

    private void colorFieldPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_colorFieldPerformed
        prefs.put("xml." + getRootElementName() + ".colorAttribute", (String) colorAttributeField.getSelectedItem());

    }//GEN-LAST:event_colorFieldPerformed

    private void nameFieldPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_nameFieldPerformed
        prefs.put("xml." + getRootElementName() + ".nameAttribute", (String) nameAttributeField.getSelectedItem());
    }//GEN-LAST:event_nameFieldPerformed
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JComboBox colorAttributeField;
    private javax.swing.JLabel colorAttributeLabel;
    private javax.swing.JComboBox nameAttributeField;
    private javax.swing.JLabel nameAttributeLabel;
    private javax.swing.JTextField rootElementField;
    private javax.swing.JLabel rootElementLabel;
    private javax.swing.JComboBox weightAttributeField;
    private javax.swing.JLabel weightAttributeLabel;
    // End of variables declaration//GEN-END:variables
}
