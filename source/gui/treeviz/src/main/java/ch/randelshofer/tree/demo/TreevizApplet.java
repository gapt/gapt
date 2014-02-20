/*
 * @(#)TreevizApplet.java  1.0  2011-01-20
 * 
 * Copyright (c) 2011 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 * 
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.demo;

import ch.randelshofer.gui.ProgressView;
import ch.randelshofer.tree.*;
import ch.randelshofer.tree.hypertree.HyperTree;
import ch.randelshofer.tree.hypertree.SwingHTView;
import ch.randelshofer.tree.circlemap.*;
import ch.randelshofer.tree.rectmap.*;
import ch.randelshofer.tree.sunray.*;
import ch.randelshofer.tree.sunburst.*;
import ch.randelshofer.text.FileSizeFormat;
import ch.randelshofer.util.Methods;
import ch.randelshofer.util.Worker;
import ch.randelshofer.util.prefs.PreferencesUtil2;
import java.awt.*;
import java.awt.event.MouseEvent;
import java.awt.event.MouseMotionAdapter;
import java.io.*;
import java.net.URL;
import java.util.HashMap;
import java.util.prefs.Preferences;
import javax.swing.*;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.TableModel;

/**
 *
 * @author werni
 */
public class TreevizApplet extends javax.swing.JApplet {

    private TreeView treeView;
    private JFileChooser directoryChooser;
    private JFileChooser fileChooser;
    private URL rootFile;
    private TreeNode rootNode;
    private Preferences prefs;
    private NodeInfo info;

    /**
     * Creates new form TreevizApplet
     */
    public TreevizApplet() {
        initComponents();
        //setSize(400, 400);
        prefs = PreferencesUtil2.userNodeForPackage(getClass());
        viewAsHypertreeRadio.setSelected(prefs.get("viewAs", "hyperbolic").equals("hyperbolic"));
        viewAsSunburstRadio.setSelected(prefs.get("viewAs", "hyperbolic").equals("sunburst"));
        viewAsSunrayRadio.setSelected(prefs.get("viewAs", "hyperbolic").equals("sunray"));
        viewAsIcicleRadio.setSelected(prefs.get("viewAs", "hyperbolic").equals("icicle"));
        viewAsIcerayRadio.setSelected(prefs.get("viewAs", "hyperbolic").equals("iceray"));
        viewAsCircleMapRadio.setSelected(prefs.get("viewAs", "hyperbolic").equals("circlemap"));
        viewAsRectangleMapRadio.setSelected(prefs.get("viewAs", "hyperbolic").equals("rectanglemap"));
        toolTipEnabledRadio.setSelected(prefs.getBoolean("toolTipEnabled", true));

        updateMaxDepth();

        statusPanel.setVisible(false);
    }

    private void updateView() {
        if (rootNode == null) {
            viewPanel.removeAll();
            statusPanel.setVisible(false);
            validate();
            repaint();

        } else {
            statusPanel.setVisible(true);
            if (viewAsHypertreeRadio.isSelected()) {
                updateHTView();
            } else if (viewAsSunburstRadio.isSelected()) {
                updateSBView();
            } else if (viewAsSunrayRadio.isSelected()) {
                updateScBView();
            } else if (viewAsIcicleRadio.isSelected()) {
                updateIcView();
            } else if (viewAsIcerayRadio.isSelected()) {
                updateIdView();
            } else if (viewAsCircleMapRadio.isSelected()) {
                updateCMView();
            } else if (viewAsRectangleMapRadio.isSelected()) {
                updateRMView();
            }
        }
    }

    private void updateToolTipEnabled() {
        if (treeView != null) {
            treeView.setToolTipEnabled(prefs.getBoolean("toolTipEnabled", true));
        }
    }

    private void updateMaxDepth() {
        maxDepthPanel.setVisible((treeView instanceof RectmapView) || (treeView instanceof CirclemapView));
        maxDepthPanel.revalidate();
        if (treeView != null) {
            treeView.setMaxDepth(prefs.getInt("maxDepth", Integer.MAX_VALUE));
        }
        switch (prefs.getInt("maxDepth", Integer.MAX_VALUE)) {
            case 1:
                maxDepth1Radio.setSelected(true);
                break;
            default:
                maxDepthInfinityRadio.setSelected(true);
                break;
        }
    }

    private void updateSBView() {
        final ProgressView p = new ProgressView("Sunburst Tree", "Calculating layout...");
        p.setIndeterminate(true);
        Worker worker = new Worker() {

            @Override
            public Object construct() {
                SunburstModel sunbursttree = new SunburstModel(rootNode, info);
                return sunbursttree;
            }

            @Override
            public void done(Object o) {
                SunburstModel model = (SunburstModel) o;
                SunburstView view = model.getView();
                treeView = view;
                //  view.setFont(new Font("Dialog", Font.PLAIN, 9));
                histogram.setWeighter(model.getInfo().getWeighter());
                histogram.setColorizer(model.getInfo().getColorizer());
                viewPanel.removeAll();
                treeView = view;
                if (info instanceof TreevizFileSystemXMLNodeInfo) {
                    JSplitPane splitPane = createSplitPane(view);
                    viewPanel.add(splitPane);
                    validate();
                    splitPane.setDividerLocation(1d);

                } else {
                    view.setToolTipEnabled(true);
                    viewPanel.add(view);
                    validate();
                }
                updateToolTipEnabled();
                updateMaxDepth();
                repaint();
            }

            @Override
            public void finished() {
                p.close();
            }
        };
        worker.start();
    }

    private void updateScBView() {
        final ProgressView p = new ProgressView("Sunray Tree", "Calculating layout...");
        p.setIndeterminate(true);
        Worker worker = new Worker() {

            @Override
            public Object construct() {
                SunrayModel scatterbursttree = new SunrayModel(rootNode, info);
                return scatterbursttree;
            }

            @Override
            public void done(Object o) {
                SunrayModel model = (SunrayModel) o;
                SunrayView view = model.getView();
                treeView = view;

                //  view.setFont(new Font("Dialog", Font.PLAIN, 9));
                histogram.setWeighter((model.getInfo().getWeighter()));
                histogram.setColorizer((model.getInfo().getColorizer()));
                viewPanel.removeAll();
                if (info instanceof TreevizFileSystemXMLNodeInfo) {
                    JSplitPane splitPane = createSplitPane(view);
                    viewPanel.add(splitPane);
                    validate();
                    splitPane.setDividerLocation(1d);

                } else {
                    view.setToolTipEnabled(true);
                    viewPanel.add(view);
                    validate();
                }
                updateToolTipEnabled();
                updateMaxDepth();
                repaint();
            }

            @Override
            public void finished() {
                p.close();
            }
        };
        worker.start();
    }

    private void updateHTView() {
        final ProgressView p = new ProgressView("Hyperbolic Tree", "Calculating layout...");
        p.setIndeterminate(true);
        Worker worker = new Worker() {

            @Override
            public Object construct() {
                HyperTree tree = new HyperTree(rootNode, info);
                return tree;
            }

            @Override
            public void done(Object o) {
                HyperTree model = (HyperTree) o;
                SwingHTView view = model.getView();
                treeView = view;
                // view.setFont(new Font("Dialog", Font.PLAIN, 9));
                histogram.setWeighter((model.getInfo().getWeighter()));
                histogram.setColorizer((model.getInfo().getColorizer()));
                viewPanel.removeAll();
                if (info instanceof TreevizFileSystemXMLNodeInfo) {
                    JSplitPane splitPane = createSplitPane(view);
                    viewPanel.add(splitPane);
                    validate();
                    splitPane.setDividerLocation(1d);

                } else {
                    view.setToolTipEnabled(true);
                    viewPanel.add(view);
                    validate();
                }
                updateToolTipEnabled();
                updateMaxDepth();
                repaint();
            }

            @Override
            public void finished() {
                p.close();
            }
        };
        worker.start();
    }

    private void updateCMView() {
        final ProgressView p = new ProgressView("Circular Treemap", "Initializing...");
        p.setCancelable(true);
        p.setIndeterminate(true);
        Worker worker = new Worker() {

            @Override
            public Object construct() {
                CirclemapModel model = new CirclemapModel(rootNode, info, p);
                return model;
            }

            @Override
            public void done(Object o) {
                if (p.isCanceled()) {
                    return;
                }
                CirclemapModel model = (CirclemapModel) o;
                CirclemapView view = model.getView();
                treeView = view;
                // view.setFont(new Font("Dialog", Font.PLAIN, 9));
                histogram.setWeighter(model.getInfo().getWeighter());
                histogram.setColorizer(model.getInfo().getColorizer());
                viewPanel.removeAll();

                if (info instanceof TreevizFileSystemXMLNodeInfo) {
                    JSplitPane splitPane = createSplitPane(view);
                    viewPanel.add(splitPane);
                    validate();
                    splitPane.setDividerLocation(1d);

                } else {
                    view.setToolTipEnabled(true);
                    viewPanel.add(view);
                    validate();
                }
                updateToolTipEnabled();
                updateMaxDepth();
                repaint();
            }

            @Override
            public void finished() {
                p.close();
            }
        };
        worker.start();
    }

    private void updateRMView() {
        final ProgressView p = new ProgressView("Rectangular Treemap", "Initializing...");
        p.setIndeterminate(true);
        Worker worker = new Worker() {

            @Override
            public Object construct() {
                RectmapModel model = new RectmapModel(rootNode, info, p);
                return model;
            }

            @Override
            public void done(Object o) {
                if (p.isCanceled()) {
                    return;
                }
                RectmapModel model = (RectmapModel) o;
                RectmapView view = model.getView();
                treeView = view;
                // view.setFont(new Font("Dialog", Font.PLAIN, 9));
                histogram.setWeighter(model.getInfo().getWeighter());
                histogram.setColorizer(model.getInfo().getColorizer());
                viewPanel.removeAll();
                if (info instanceof TreevizFileSystemXMLNodeInfo) {
                    JSplitPane splitPane = createSplitPane(view);
                    viewPanel.add(splitPane);
                    validate();
                    splitPane.setDividerLocation(1d);

                } else {
                    view.setToolTipEnabled(true);
                    viewPanel.add(view);
                    validate();
                }
                updateToolTipEnabled();
                updateMaxDepth();
                repaint();
            }

            @Override
            public void finished() {
                p.close();
            }
        };
        worker.start();
    }

    private void updateIcView() {
        final ProgressView p = new ProgressView("Icicle Tree", "Calculating layout...");
        p.setIndeterminate(true);
        Worker worker = new Worker() {

            @Override
            public Object construct() {
                IcicleModel tree = new IcicleModel(rootNode, info);
                return tree;
            }

            @Override
            public void done(Object o) {
                IcicleModel model = (IcicleModel) o;
                IcicleView view = model.getView();
                treeView = view;
                //  view.setFont(new Font("Dialog", Font.PLAIN, 9));
                histogram.setWeighter(model.getInfo().getWeighter());
                histogram.setColorizer(model.getInfo().getColorizer());
                viewPanel.removeAll();
                if (info instanceof TreevizFileSystemXMLNodeInfo) {
                    JSplitPane splitPane = createSplitPane(view);
                    viewPanel.add(splitPane);
                    validate();
                    splitPane.setDividerLocation(1d);

                } else {
                    view.setToolTipEnabled(true);
                    viewPanel.add(view);
                    validate();
                }
                updateToolTipEnabled();
                updateMaxDepth();
                repaint();
            }

            @Override
            public void finished() {
                p.close();
            }
        };
        worker.start();
    }

    private void updateIdView() {
        final ProgressView p = new ProgressView("Iceray Tree", "Calculating layout...");
        p.setIndeterminate(true);
        Worker worker = new Worker() {

            @Override
            public Object construct() {
                IcerayModel tree = new IcerayModel(rootNode, info);
                return tree;
            }

            @Override
            public void done(Object o) {
                IcerayModel model = (IcerayModel) o;
                IcerayView view = model.getView();
                treeView = view;
                //  view.setFont(new Font("Dialog", Font.PLAIN, 9));
                histogram.setWeighter(model.getInfo().getWeighter());
                histogram.setColorizer(model.getInfo().getColorizer());
                viewPanel.removeAll();
                if (info instanceof TreevizFileSystemXMLNodeInfo) {
                    JSplitPane splitPane = createSplitPane(view);
                    viewPanel.add(splitPane);
                    validate();
                    splitPane.setDividerLocation(1d);

                } else {
                    view.setToolTipEnabled(true);
                    viewPanel.add(view);
                    validate();
                }
                updateToolTipEnabled();
                updateMaxDepth();
                repaint();
            }

            @Override
            public void finished() {
                p.close();
            }
        };
        worker.start();
    }

    private JSplitPane createSplitPane(Component view) {
        JSplitPane splitPane = new JSplitPane();
        splitPane.setOneTouchExpandable(true);
        splitPane.setLeftComponent(view);

        JTabbedPane tabbedPane = new JTabbedPane();
        tabbedPane.add("Table", createTablePanel(view));
        tabbedPane.add("Info", createInfoPanel(view));

        splitPane.setRightComponent(tabbedPane);
        return splitPane;
    }

    private JComponent createTablePanel(Component view) {
        final JTable table = new JTable();
        // table.setAutoResizeMode(JTable.AUTO_RESIZE_OFF);
        TableModel tm = ((TreevizFileSystemXMLNodeInfo) info).getUserTable();
        table.setModel(tm);
        Methods.invokeIfExists(table, "setAutoCreateRowSorter", true);


        table.setDefaultRenderer(Long.class, new DefaultTableCellRenderer() {

            @Override
            public Component getTableCellRendererComponent(JTable table, Object value,
                    boolean isSelected, boolean hasFocus, int row, int column) {
                if (value instanceof Long) {
                    value = FileSizeFormat.getInstance().format((Long) value);
                }
                return super.getTableCellRendererComponent(table, value, isSelected, hasFocus, row, column);
            }
        });
        table.getSelectionModel().addListSelectionListener(new ListSelectionListener() {

            @Override
            public void valueChanged(ListSelectionEvent e) {
                if (!e.getValueIsAdjusting()) {
                    HashMap<String, TreevizFileSystemXMLNode> selectedUsers = new HashMap<String, TreevizFileSystemXMLNode>();
                    TreevizFileSystemXMLNodeInfo.InfoTableModel model = (TreevizFileSystemXMLNodeInfo.InfoTableModel) table.getModel();
                    ListSelectionModel lsm = table.getSelectionModel();
                    for (int i = 0, n = model.getRowCount(); i < n; i++) {
                        if (lsm.isSelectedIndex(i)) {
                            TreevizFileSystemXMLNode user;
                            try {
                                user = model.getRowObject((Integer) Methods.invoke(Methods.invoke(table, "getRowSorter"), "convertRowIndexToModel", i));
                            } catch (NoSuchMethodException ex) {
                                user = model.getRowObject(i);
                            }
                            selectedUsers.put((String) user.getAttribute("id"), user);
                        }
                    }
                    ((TreevizFileSystemXMLNodeInfo) info).setSelectedUsers(selectedUsers);

                }
            }
        });
        JScrollPane scrollPane = new JScrollPane();
        scrollPane.setMinimumSize(new Dimension(0, 0));
        scrollPane.setViewportView(table);
        return scrollPane;
    }

    private JComponent createInfoPanel(Component view) {
        final JLabel infoLabel = new JLabel();
        infoLabel.setVerticalAlignment(JLabel.TOP);
        if (view instanceof TreeView) {
            final TreeView treeView = (TreeView) view;
            view.addMouseMotionListener(new MouseMotionAdapter() {

                @Override
                public void mouseMoved(MouseEvent evt) {
                    infoLabel.setText(treeView.getInfoText(evt));
                }
            });
        }

        JScrollPane scrollPane = new JScrollPane();
        scrollPane.setMinimumSize(new Dimension(0, 0));
        scrollPane.setViewportView(infoLabel);
        return scrollPane;
    }

    @Override
    public void setEnabled(boolean b) {
        super.setEnabled(b);
        if (treeView != null) {
            ((Component) treeView).setEnabled(b);

        }
        if (histogram != null) {
            histogram.setEnabled(b);
        }
        if (maxDepth1Radio != null) {
            maxDepth1Radio.setEnabled(b);
            maxDepthInfinityRadio.setEnabled(b);
        }
    }

    /** Initializes the applet TreevizApplet */
    @Override
    public void init() {
        new Worker() {

            @Override
            protected Object construct() throws Exception {
                if (getParameter("file") == null) {
                    throw new IllegalArgumentException("The Applet-Parameter \"file\" has not been specified.");
                }
                URL fileURL = new URL(getDocumentBase(), getParameter("file"));

                prefs.put("xml.nameAttribute", getParameter("nameAttribute", "name"));
                prefs.put("xml.weightAttribute", getParameter("weightAttribute", "size"));
                prefs.put("xml.colorAttribute", getParameter("colorAttribute", "color"));
                openURL(fileURL);
                return null;
            }

            @Override
            protected void failed(Throwable error) {
                error.printStackTrace();
                getContentPane().removeAll();
                setJMenuBar(null);
                getContentPane().setLayout(new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));
                add(new JLabel(getAppletInfo()));
                add(new JLabel(" "));
                add(new JLabel("<html><b>Sorry, couldn't initialize the applet:</b><br>" + error.getMessage()));
                add(new JLabel(" "));
                StringBuilder buf = new StringBuilder("<html>The Applet supports the following parameters:<table>");
                for (String[] row : getParameterInfo()) {
                    buf.append("<tr>");
                    for (String column : row) {
                        buf.append("<td>");
                        buf.append(column);
                        buf.append("</td>");
                    }
                    buf.append("</tr>");
                }
                buf.append("</table>");
                add(new JLabel(buf.toString()));
                ((JComponent) getContentPane()).revalidate();
            }
        }.start();
    }

    /** Returns version and copyright information. */
    @Override
    public String getAppletInfo() {
        return getAppletName() + " " + getAppletVersion() + "\n"
                + getAppletCopyright();
    }

    public String getAppletCopyright() {
        return "© Werner Randelshofer";
    }

    public String getAppletName() {
        String name = getClass().getName();
        int p = name.lastIndexOf('.');
        if (p != -1) {
            name = name.substring(p + 1);
        }

        if (name.endsWith("Applet")) {
            name = name.substring(0, name.length() - 6);
        }

        return name;
    }

    protected String getAppletVersion() {
        String version = TreevizApplet.class.getPackage().getImplementationVersion();
        return version == null ? "" : version;
    }

    public String getParameter(String name, String defaultValue) {
        String value = getParameter(name);
        return value == null ? defaultValue : value;
    }

    @Override
    public String getParameter(String name) {
        try {
            return super.getParameter(name);
        } catch (NullPointerException e) {
            return null;
        }
    }

    /**
     * Returns information about the parameters supported
     * by this applet.
     */
    @Override
    public String[][] getParameterInfo() {


        String[][] info = {
            // Parameter Name,  Kind of Value, Description

            {"file", "URL", "The file to be displayed"},
            {"weightAttribute", "String", "The name of the XML attribute used to weight a tree node. Default value: \"size\"."},
            {"colorAttribute", "String", "The name of the XML attribute used to color a tree node. Default value: \"created\"."},
            {"nameAttribute", "String", "The name of the XML attribute used to name a tree node. Default value: \"name\"."},};
        return info;
    }

    private void openURL(URL file) {
        rootFile = file;
        new Worker<DemoTree>() {

            @Override
            public DemoTree construct() throws Exception {
                DemoTree tree;

                if (rootFile.getPath().endsWith(".txt")) {
                    tree = new ManyEyesTree(rootFile);
                    return tree;
                } else {

                    // Try TreevizFileSystemXMLTree
                    try {
                        tree = new TreevizFileSystemXMLTree(rootFile);
                        return tree;
                    } catch (IOException ex) {
                        if (ex.getMessage() != null && ex.getMessage().equals("Aborted")) {
                            throw ex;
                        }
                        // ex.printStackTrace();
                        // continue
                    }

                    // Try generic XMLTree
                    tree = new XMLTree(rootFile);
                    return tree;
                }
            }

            @Override
            public void done(DemoTree result) {
                rootNode = ((DemoTree) result).getRoot();
                info = ((DemoTree) result).getInfo();
                //setTitle("Tree Visualizer: " + info.getName(new TreePath2(rootNode)));
                updateView();
            }

            @Override
            public void failed(Throwable t) {
                t.printStackTrace();
            }
        }.start();
    }

    /** This method is called from within the init() method to
     * initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is
     * always regenerated by the Form Editor.
     */
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {
        java.awt.GridBagConstraints gridBagConstraints;

        viewGroup = new javax.swing.ButtonGroup();
        viewPanel = new javax.swing.JPanel();
        statusPanel = new javax.swing.JPanel();
        histogram = new ch.randelshofer.tree.demo.JHistogram();
        maxDepthPanel = new javax.swing.JPanel();
        maxDepthInfinityRadio = new javax.swing.JRadioButton();
        maxDepth1Radio = new javax.swing.JRadioButton();
        jMenuBar1 = new javax.swing.JMenuBar();
        viewMenu = new javax.swing.JMenu();
        viewAsHypertreeRadio = new javax.swing.JRadioButtonMenuItem();
        viewAsSunburstRadio = new javax.swing.JRadioButtonMenuItem();
        viewAsSunrayRadio = new javax.swing.JRadioButtonMenuItem();
        viewAsIcicleRadio = new javax.swing.JRadioButtonMenuItem();
        viewAsIcerayRadio = new javax.swing.JRadioButtonMenuItem();
        viewAsCircleMapRadio = new javax.swing.JRadioButtonMenuItem();
        viewAsRectangleMapRadio = new javax.swing.JRadioButtonMenuItem();
        jSeparator1 = new javax.swing.JSeparator();
        toolTipEnabledRadio = new javax.swing.JCheckBoxMenuItem();

        FormListener formListener = new FormListener();

        viewPanel.setLayout(new java.awt.BorderLayout());
        getContentPane().add(viewPanel, java.awt.BorderLayout.CENTER);

        statusPanel.setLayout(new java.awt.GridBagLayout());

        histogram.addMouseListener(formListener);
        histogram.setLayout(new java.awt.FlowLayout());
        statusPanel.add(histogram, new java.awt.GridBagConstraints());

        maxDepthPanel.setLayout(new java.awt.GridBagLayout());

        maxDepthInfinityRadio.setText("Show full depth");
        maxDepthInfinityRadio.addActionListener(formListener);
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.NORTHWEST;
        maxDepthPanel.add(maxDepthInfinityRadio, gridBagConstraints);

        maxDepth1Radio.setText("Show current depth only");
        maxDepth1Radio.addActionListener(formListener);
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.NORTHWEST;
        maxDepthPanel.add(maxDepth1Radio, gridBagConstraints);

        statusPanel.add(maxDepthPanel, new java.awt.GridBagConstraints());

        getContentPane().add(statusPanel, java.awt.BorderLayout.SOUTH);

        viewMenu.setText("View");

        viewGroup.add(viewAsHypertreeRadio);
        viewAsHypertreeRadio.setSelected(true);
        viewAsHypertreeRadio.setText("Hyperbolic Tree");
        viewAsHypertreeRadio.addItemListener(formListener);
        viewMenu.add(viewAsHypertreeRadio);

        viewGroup.add(viewAsSunburstRadio);
        viewAsSunburstRadio.setText("Sunburst Tree");
        viewAsSunburstRadio.addItemListener(formListener);
        viewMenu.add(viewAsSunburstRadio);

        viewGroup.add(viewAsSunrayRadio);
        viewAsSunrayRadio.setText("Sunray Tree");
        viewAsSunrayRadio.addItemListener(formListener);
        viewMenu.add(viewAsSunrayRadio);

        viewGroup.add(viewAsIcicleRadio);
        viewAsIcicleRadio.setText("Icicle Tree");
        viewAsIcicleRadio.addItemListener(formListener);
        viewMenu.add(viewAsIcicleRadio);

        viewGroup.add(viewAsIcerayRadio);
        viewAsIcerayRadio.setText("Iceray Tree");
        viewAsIcerayRadio.addItemListener(formListener);
        viewMenu.add(viewAsIcerayRadio);

        viewGroup.add(viewAsCircleMapRadio);
        viewAsCircleMapRadio.setText("Circular Treemap");
        viewAsCircleMapRadio.addItemListener(formListener);
        viewMenu.add(viewAsCircleMapRadio);

        viewGroup.add(viewAsRectangleMapRadio);
        viewAsRectangleMapRadio.setText("Rectangular Treemap");
        viewAsRectangleMapRadio.addItemListener(formListener);
        viewMenu.add(viewAsRectangleMapRadio);
        viewMenu.add(jSeparator1);

        toolTipEnabledRadio.setSelected(true);
        toolTipEnabledRadio.setText("Show Tooltips");
        toolTipEnabledRadio.addActionListener(formListener);
        viewMenu.add(toolTipEnabledRadio);

        jMenuBar1.add(viewMenu);

        setJMenuBar(jMenuBar1);
    }

    // Code for dispatching events from components to event handlers.

    private class FormListener implements java.awt.event.ActionListener, java.awt.event.ItemListener, java.awt.event.MouseListener {
        FormListener() {}
        public void actionPerformed(java.awt.event.ActionEvent evt) {
            if (evt.getSource() == maxDepthInfinityRadio) {
                TreevizApplet.this.maxDepthInfinityRadiomaxDepthRadioPerformed(evt);
            }
            else if (evt.getSource() == maxDepth1Radio) {
                TreevizApplet.this.maxDepth1RadiomaxDepthRadioPerformed(evt);
            }
            else if (evt.getSource() == toolTipEnabledRadio) {
                TreevizApplet.this.toolTipEnabledRadiotooltipsEnabledPerformed(evt);
            }
        }

        public void itemStateChanged(java.awt.event.ItemEvent evt) {
            if (evt.getSource() == viewAsHypertreeRadio) {
                TreevizApplet.this.viewAsChanged(evt);
            }
            else if (evt.getSource() == viewAsSunburstRadio) {
                TreevizApplet.this.viewAsChanged(evt);
            }
            else if (evt.getSource() == viewAsSunrayRadio) {
                TreevizApplet.this.viewAsChanged(evt);
            }
            else if (evt.getSource() == viewAsIcicleRadio) {
                TreevizApplet.this.viewAsChanged(evt);
            }
            else if (evt.getSource() == viewAsIcerayRadio) {
                TreevizApplet.this.viewAsChanged(evt);
            }
            else if (evt.getSource() == viewAsCircleMapRadio) {
                TreevizApplet.this.viewAsChanged(evt);
            }
            else if (evt.getSource() == viewAsRectangleMapRadio) {
                TreevizApplet.this.viewAsChanged(evt);
            }
        }

        public void mouseClicked(java.awt.event.MouseEvent evt) {
            if (evt.getSource() == histogram) {
                TreevizApplet.this.histogramtoggleHistogram(evt);
            }
        }

        public void mouseEntered(java.awt.event.MouseEvent evt) {
        }

        public void mouseExited(java.awt.event.MouseEvent evt) {
        }

        public void mousePressed(java.awt.event.MouseEvent evt) {
        }

        public void mouseReleased(java.awt.event.MouseEvent evt) {
        }
    }// </editor-fold>//GEN-END:initComponents

    private void histogramtoggleHistogram(java.awt.event.MouseEvent evt) {//GEN-FIRST:event_histogramtoggleHistogram
        if (info != null) {
            setEnabled(false);
            new Worker() {

                @Override
                protected Object construct() throws Exception {
                    info.toggleColorWeighter();
                    return null;
                }

                @Override
                protected void finished() {
                    histogram.setColorizer(info.getColorizer());
                    histogram.setWeighter(info.getWeighter());
                    histogram.repaint();
                    if (treeView != null) {
                        treeView.repaintView();
                    }
                    setEnabled(true);

                }
            }.start();
        }
}//GEN-LAST:event_histogramtoggleHistogram

    private void maxDepthInfinityRadiomaxDepthRadioPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_maxDepthInfinityRadiomaxDepthRadioPerformed

        prefs.putInt("maxDepth", maxDepth1Radio.isSelected() ? 1 : Integer.MAX_VALUE);
        updateMaxDepth();
    }//GEN-LAST:event_maxDepthInfinityRadiomaxDepthRadioPerformed

    private void maxDepth1RadiomaxDepthRadioPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_maxDepth1RadiomaxDepthRadioPerformed

        prefs.putInt("maxDepth", maxDepth1Radio.isSelected() ? 1 : Integer.MAX_VALUE);
        updateMaxDepth();
    }//GEN-LAST:event_maxDepth1RadiomaxDepthRadioPerformed

    private void viewAsChanged(java.awt.event.ItemEvent evt) {//GEN-FIRST:event_viewAsChanged
        String view = null;
        if (viewAsHypertreeRadio.isSelected()) {
            view = "hyperbolic";
        } else if (viewAsSunburstRadio.isSelected()) {
            view = "sunburst";
        } else if (viewAsSunrayRadio.isSelected()) {
            view = "sunray";
        } else if (viewAsIcicleRadio.isSelected()) {
            view = "icicle";
        } else if (viewAsIcerayRadio.isSelected()) {
            view = "iceray";
        } else if (viewAsCircleMapRadio.isSelected()) {
            view = "circlemap";
        } else if (viewAsRectangleMapRadio.isSelected()) {
            view = "rectanglemap";
        }
        if (view != null) {
            prefs.put("viewAs", view);
            updateView();
        }
    }//GEN-LAST:event_viewAsChanged

    private void toolTipEnabledRadiotooltipsEnabledPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_toolTipEnabledRadiotooltipsEnabledPerformed
        prefs.putBoolean("toolTipEnabled", toolTipEnabledRadio.isSelected());
        updateToolTipEnabled();
}//GEN-LAST:event_toolTipEnabledRadiotooltipsEnabledPerformed
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private ch.randelshofer.tree.demo.JHistogram histogram;
    private javax.swing.JMenuBar jMenuBar1;
    private javax.swing.JSeparator jSeparator1;
    private javax.swing.JRadioButton maxDepth1Radio;
    private javax.swing.JRadioButton maxDepthInfinityRadio;
    private javax.swing.JPanel maxDepthPanel;
    private javax.swing.JPanel statusPanel;
    private javax.swing.JCheckBoxMenuItem toolTipEnabledRadio;
    private javax.swing.JRadioButtonMenuItem viewAsCircleMapRadio;
    private javax.swing.JRadioButtonMenuItem viewAsHypertreeRadio;
    private javax.swing.JRadioButtonMenuItem viewAsIcerayRadio;
    private javax.swing.JRadioButtonMenuItem viewAsIcicleRadio;
    private javax.swing.JRadioButtonMenuItem viewAsRectangleMapRadio;
    private javax.swing.JRadioButtonMenuItem viewAsSunburstRadio;
    private javax.swing.JRadioButtonMenuItem viewAsSunrayRadio;
    private javax.swing.ButtonGroup viewGroup;
    private javax.swing.JMenu viewMenu;
    private javax.swing.JPanel viewPanel;
    // End of variables declaration//GEN-END:variables
}
