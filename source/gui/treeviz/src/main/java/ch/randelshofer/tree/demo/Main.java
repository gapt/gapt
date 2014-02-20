/*
 * @(#)Main.java  1.1.1  2011-08-19
 *
 * Copyright (c) 2007-2011 Werner Randelshofer, Goldau, Switzerland.
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
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.awt.event.MouseEvent;
import java.awt.event.MouseMotionAdapter;
import java.awt.print.PageFormat;
import java.awt.print.Pageable;
import java.awt.print.Paper;
import java.awt.print.Printable;
import java.awt.print.PrinterException;
import java.awt.print.PrinterJob;
import java.io.*;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.prefs.Preferences;
import javax.print.attribute.HashPrintRequestAttributeSet;
import javax.print.attribute.PrintRequestAttributeSet;
import javax.print.attribute.standard.PrinterResolution;
import javax.swing.*;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.TableModel;

/**
 *
 * @author werni
 * @version 1.1.1 2011-08-19 Shows an error dialog when the tree structure could
 * not be created. <br>1.0.1 2009-01-28 Fixed tooltip enabling. <br>1.0
 * 2007-09-16 Created.
 */
public class Main extends javax.swing.JFrame {

    private TreeView treeView;
    private JFileChooser directoryChooser;
    private JFileChooser fileChooser;
    private File rootFile;
    private TreeNode rootNode;
    private Preferences prefs;
    private NodeInfo info;
    private DropTargetListener dropHandler = new DropTargetListener() {
        /**
         * Called when a drag operation has encountered the
         * <code>DropTarget</code>. <P>
         *
         * @param dtde the <code>DropTargetDragEvent</code>
         */
        @Override
        public void dragEnter(DropTargetDragEvent event) {
            if (event.isDataFlavorSupported(DataFlavor.javaFileListFlavor)) {
                event.acceptDrag(DnDConstants.ACTION_COPY);
            } else {
                event.rejectDrag();
            }
        }

        /**
         * The drag operation has departed the
         * <code>DropTarget</code> without dropping. <P>
         *
         * @param dte the <code>DropTargetEvent</code>
         */
        @Override
        public void dragExit(DropTargetEvent event) {
            // Nothing to do
        }

        /**
         * Called when a drag operation is ongoing on the
         * <code>DropTarget</code>. <P>
         *
         * @param dtde the <code>DropTargetDragEvent</code>
         */
        @Override
        public void dragOver(DropTargetDragEvent event) {
            if (event.isDataFlavorSupported(DataFlavor.javaFileListFlavor)) {
                event.acceptDrag(DnDConstants.ACTION_COPY);
            } else {
                event.rejectDrag();
            }
        }

        /**
         * The drag operation has terminated with a drop on this
         * <code>DropTarget</code>. This method is responsible for undertaking
         * the transfer of the data associated with the gesture. The
         * <code>DropTargetDropEvent</code> provides a means to obtain a
         * <code>Transferable</code> object that represents the data object(s)
         * to be transfered.<P> From this method, the
         * <code>DropTargetListener</code> shall accept or reject the drop via
         * the acceptDrop(int dropAction) or rejectDrop() methods of the
         * <code>DropTargetDropEvent</code> parameter. <P> Subsequent to
         * acceptDrop(), but not before,
         * <code>DropTargetDropEvent</code>'s getTransferable() method may be
         * invoked, and data transfer may be performed via the returned
         * <code>Transferable</code>'s getTransferData() method. <P> At the
         * completion of a drop, an implementation of this method is required to
         * signal the success/failure of the drop by passing an appropriate
         * <code>boolean</code> to the
         * <code>DropTargetDropEvent</code>'s dropComplete(boolean success)
         * method. <P> Note: The actual processing of the data transfer is not
         * required to finish before this method returns. It may be deferred
         * until later. <P>
         *
         * @param dtde the <code>DropTargetDropEvent</code>
         */
        @Override
        public void drop(DropTargetDropEvent event) {
            if (event.isDataFlavorSupported(DataFlavor.javaFileListFlavor)) {
                event.acceptDrop(DnDConstants.ACTION_COPY);

                try {
                    java.util.List<File> files = (java.util.List<File>) event.getTransferable().getTransferData(DataFlavor.javaFileListFlavor);
                    if (files.size() == 1) {

                        File file = files.get(0);
                        if (file.isDirectory()) {
                            openDirectory(file);
                        } else {
                            openFile(file);
                        }
                    }
                } catch (IOException e) {
                    JOptionPane.showConfirmDialog(
                            Main.this,
                            "Could not access the dropped data.",
                            "Treeviz: Drop Failed",
                            JOptionPane.DEFAULT_OPTION, JOptionPane.INFORMATION_MESSAGE);
                } catch (UnsupportedFlavorException e) {
                    JOptionPane.showConfirmDialog(
                            Main.this,
                            "Unsupported data flavor.",
                            "Treeviz: Drop Failed",
                            JOptionPane.DEFAULT_OPTION, JOptionPane.INFORMATION_MESSAGE);
                }
            } else {
                event.rejectDrop();
            }
        }

        /**
         * Called if the user has modified the current drop gesture. <P>
         *
         * @param dtde the <code>DropTargetDragEvent</code>
         */
        @Override
        public void dropActionChanged(DropTargetDragEvent event) {
            // Nothing to do
        }
    };

    /**
     * Creates new form Main.
     */
    public Main() {
        initComponents();
        setSize(400, 400);
        prefs = PreferencesUtil2.userNodeForPackage(getClass());

        String preferredView = prefs.get("viewAs", "hyperbolic");
        for (Enumeration<AbstractButton> e = viewAsButtonGroup.getElements(); e.hasMoreElements();) {
            AbstractButton b = e.nextElement();
            b.setSelected(preferredView.equals(b.getActionCommand()));
        }
        /*
         viewAsHypertreeRadio.setSelected(prefs.get("viewAs", "hyperbolic").equals(viewAsHypertreeRadio.getActionCommand()));
         viewAsSunburstRadio.setSelected(prefs.get("viewAs", "hyperbolic").equals("sunburst"));
         viewAsSunrayRadio.setSelected(prefs.get("viewAs", "hyperbolic").equals("sunray"));
         viewAsIcicleRadio.setSelected(prefs.get("viewAs", "hyperbolic").equals("icicle"));
         viewAsIcerayRadio.setSelected(prefs.get("viewAs", "hyperbolic").equals("iceray"));
         viewAsCircleMapRadio.setSelected(prefs.get("viewAs", "hyperbolic").equals("circlemap"));
         viewAsRectangleMapRadio.setSelected(prefs.get("viewAs", "hyperbolic").equals("rectanglemap"));
         */
        multilineLabelsRadio.setSelected(prefs.getBoolean("multilineLabels", false));
        toolTipEnabledRadio.setSelected(prefs.getBoolean("toolTipEnabled", true));

        updateMaxDepth();

        new DropTarget(this, dropHandler);
        new DropTarget(getContentPane(), dropHandler);
        new DropTarget(viewPanel, dropHandler);
        statusPanel.setVisible(false);
    }

    private void updateView() {
        // remove view panel so that memory can be freed
        if (rootNode == null) {
            statusPanel.setVisible(false);

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
        validate();
        repaint();
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
        viewPanel.removeAll();
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
                new DropTarget(view, dropHandler);
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
        viewPanel.removeAll();
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
                new DropTarget(view, dropHandler);
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
        viewPanel.removeAll();
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
                new DropTarget(view, dropHandler);
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
        viewPanel.removeAll();
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
                new DropTarget(view, dropHandler);
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
        final boolean isMultiline = prefs.getBoolean("multilineLabels", false);
        if (treeView instanceof RectmapView) {
            RectmapView rv = (RectmapView) treeView;
            rv.setDraw(isMultiline ?//
                    new MultilineRectmapDraw(rv.getModel()) ://
                    new RectmapDraw(rv.getModel())//
                    );
            rv.repaint();
            return;
        }

        final ProgressView p = new ProgressView("Rectangular Treemap", "Initializing...");
        p.setIndeterminate(true);
        viewPanel.removeAll();
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
                view.setDraw(isMultiline ?//
                        new MultilineRectmapDraw(view.getModel()) ://
                        new RectmapDraw(view.getModel())//
                        );
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
                new DropTarget(view, dropHandler);
                repaint();
            }

            @Override
            protected void failed(Throwable error) {
                JOptionPane.showMessageDialog(Main.this, "<html>Could not create a rectangular treemap.<br>" + error.getMessage(), "Treeviz", JOptionPane.ERROR_MESSAGE);
                error.printStackTrace();
            }

            @Override
            public void finished() {
                p.close();
            }
        };
        worker.start();
    }

    private void updateIcView() {
        final boolean isMultiline = prefs.getBoolean("multilineLabels", false);
        if (treeView instanceof IcicleView) {
            IcicleView rv = (IcicleView) treeView;
            rv.setDraw(isMultiline ?//
                    new MultilineIcicleDraw(rv.getModel()) ://
                    new IcicleDraw(rv.getModel())//
                    );
            rv.repaint();
            return;
        }
        final ProgressView p = new ProgressView("Icicle Tree", "Calculating layout...");
        p.setIndeterminate(true);
        viewPanel.removeAll();
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
                view.setDraw(isMultiline ?//
                        new MultilineIcicleDraw(view.getModel()) ://
                        new IcicleDraw(view.getModel())//
                        );
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
                new DropTarget(view, dropHandler);
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
        final boolean isMultiline = prefs.getBoolean("multilineLabels", false);
        if (treeView instanceof IcerayView) {
            IcerayView rv = (IcerayView) treeView;
            rv.setDraw(isMultiline ?//
                    new MultilineIcerayDraw(rv.getModel()) ://
                    new IcerayDraw(rv.getModel())//
                    );
            rv.repaint();
            return;
        }
        final ProgressView p = new ProgressView("Iceray Tree", "Calculating layout...");
        p.setIndeterminate(true);
        viewPanel.removeAll();
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
                view.setDraw(isMultiline ?//
                        new MultilineIcerayDraw(view.getModel()) ://
                        new IcerayDraw(view.getModel())//
                        );
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
                new DropTarget(view, dropHandler);
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

    /**
     * This method is called from within the constructor to initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is always
     * regenerated by the Form Editor.
     */
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {
        java.awt.GridBagConstraints gridBagConstraints;

        viewAsButtonGroup = new javax.swing.ButtonGroup();
        maxDepthButtonGroup = new javax.swing.ButtonGroup();
        viewPanel = new javax.swing.JPanel();
        statusPanel = new javax.swing.JPanel();
        histogram = new ch.randelshofer.tree.demo.JHistogram();
        maxDepthPanel = new javax.swing.JPanel();
        maxDepthInfinityRadio = new javax.swing.JRadioButton();
        maxDepth1Radio = new javax.swing.JRadioButton();
        jMenuBar1 = new javax.swing.JMenuBar();
        fileMenu = new javax.swing.JMenu();
        openDirectoryMenuItem = new javax.swing.JMenuItem();
        openFileMenuItem = new javax.swing.JMenuItem();
        printMenuItem = new javax.swing.JMenuItem();
        viewMenu = new javax.swing.JMenu();
        viewAsHypertreeRadio = new javax.swing.JRadioButtonMenuItem();
        viewAsSunburstRadio = new javax.swing.JRadioButtonMenuItem();
        viewAsSunrayRadio = new javax.swing.JRadioButtonMenuItem();
        viewAsIcicleRadio = new javax.swing.JRadioButtonMenuItem();
        viewAsIcerayRadio = new javax.swing.JRadioButtonMenuItem();
        viewAsCircleMapRadio = new javax.swing.JRadioButtonMenuItem();
        viewAsRectangleMapRadio = new javax.swing.JRadioButtonMenuItem();
        jSeparator1 = new javax.swing.JSeparator();
        multilineLabelsRadio = new javax.swing.JCheckBoxMenuItem();
        toolTipEnabledRadio = new javax.swing.JCheckBoxMenuItem();
        helpMenu = new javax.swing.JMenu();
        aboutMenuItem = new javax.swing.JMenuItem();

        setDefaultCloseOperation(javax.swing.WindowConstants.EXIT_ON_CLOSE);
        setTitle("Tree Visualizer");

        viewPanel.setLayout(new java.awt.BorderLayout());
        getContentPane().add(viewPanel, java.awt.BorderLayout.CENTER);

        statusPanel.setLayout(new java.awt.GridBagLayout());

        histogram.addMouseListener(new java.awt.event.MouseAdapter() {
            public void mouseClicked(java.awt.event.MouseEvent evt) {
                toggleHistogram(evt);
            }
        });
        histogram.setLayout(new java.awt.FlowLayout());
        statusPanel.add(histogram, new java.awt.GridBagConstraints());

        maxDepthPanel.setLayout(new java.awt.GridBagLayout());

        maxDepthButtonGroup.add(maxDepthInfinityRadio);
        maxDepthInfinityRadio.setText("Show full depth");
        maxDepthInfinityRadio.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                maxDepthRadioPerformed(evt);
            }
        });
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.NORTHWEST;
        maxDepthPanel.add(maxDepthInfinityRadio, gridBagConstraints);

        maxDepthButtonGroup.add(maxDepth1Radio);
        maxDepth1Radio.setText("Show current depth only");
        maxDepth1Radio.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                maxDepthRadioPerformed(evt);
            }
        });
        gridBagConstraints = new java.awt.GridBagConstraints();
        gridBagConstraints.gridx = 0;
        gridBagConstraints.anchor = java.awt.GridBagConstraints.NORTHWEST;
        maxDepthPanel.add(maxDepth1Radio, gridBagConstraints);

        statusPanel.add(maxDepthPanel, new java.awt.GridBagConstraints());

        getContentPane().add(statusPanel, java.awt.BorderLayout.SOUTH);

        fileMenu.setText("File");

        openDirectoryMenuItem.setText("Open Directory…");
        openDirectoryMenuItem.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                openDirectory(evt);
            }
        });
        fileMenu.add(openDirectoryMenuItem);

        openFileMenuItem.setText("Open File...");
        openFileMenuItem.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                openFile(evt);
            }
        });
        fileMenu.add(openFileMenuItem);

        printMenuItem.setText("Print");
        printMenuItem.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                printPerformed(evt);
            }
        });
        fileMenu.add(printMenuItem);

        jMenuBar1.add(fileMenu);

        viewMenu.setText("View");

        viewAsButtonGroup.add(viewAsHypertreeRadio);
        viewAsHypertreeRadio.setSelected(true);
        viewAsHypertreeRadio.setText("Hyperbolic Tree");
        viewAsHypertreeRadio.setActionCommand("hyperbolic");
        viewAsHypertreeRadio.addItemListener(new java.awt.event.ItemListener() {
            public void itemStateChanged(java.awt.event.ItemEvent evt) {
                viewAsItemChanged(evt);
            }
        });
        viewMenu.add(viewAsHypertreeRadio);

        viewAsButtonGroup.add(viewAsSunburstRadio);
        viewAsSunburstRadio.setText("Sunburst Tree");
        viewAsSunburstRadio.setActionCommand("sunburst");
        viewAsSunburstRadio.addItemListener(new java.awt.event.ItemListener() {
            public void itemStateChanged(java.awt.event.ItemEvent evt) {
                viewAsItemChanged(evt);
            }
        });
        viewMenu.add(viewAsSunburstRadio);

        viewAsButtonGroup.add(viewAsSunrayRadio);
        viewAsSunrayRadio.setText("Sunray Tree");
        viewAsSunrayRadio.setActionCommand("sunray");
        viewAsSunrayRadio.addItemListener(new java.awt.event.ItemListener() {
            public void itemStateChanged(java.awt.event.ItemEvent evt) {
                viewAsItemChanged(evt);
            }
        });
        viewMenu.add(viewAsSunrayRadio);

        viewAsButtonGroup.add(viewAsIcicleRadio);
        viewAsIcicleRadio.setText("Icicle Tree");
        viewAsIcicleRadio.setActionCommand("icicle");
        viewAsIcicleRadio.addItemListener(new java.awt.event.ItemListener() {
            public void itemStateChanged(java.awt.event.ItemEvent evt) {
                viewAsItemChanged(evt);
            }
        });
        viewMenu.add(viewAsIcicleRadio);

        viewAsButtonGroup.add(viewAsIcerayRadio);
        viewAsIcerayRadio.setText("Iceray Tree");
        viewAsIcerayRadio.setActionCommand("iceray");
        viewAsIcerayRadio.addItemListener(new java.awt.event.ItemListener() {
            public void itemStateChanged(java.awt.event.ItemEvent evt) {
                viewAsItemChanged(evt);
            }
        });
        viewMenu.add(viewAsIcerayRadio);

        viewAsButtonGroup.add(viewAsCircleMapRadio);
        viewAsCircleMapRadio.setText("Circular Treemap");
        viewAsCircleMapRadio.setActionCommand("circlemap");
        viewAsCircleMapRadio.addItemListener(new java.awt.event.ItemListener() {
            public void itemStateChanged(java.awt.event.ItemEvent evt) {
                viewAsItemChanged(evt);
            }
        });
        viewMenu.add(viewAsCircleMapRadio);

        viewAsButtonGroup.add(viewAsRectangleMapRadio);
        viewAsRectangleMapRadio.setText("Rectangular Treemap");
        viewAsRectangleMapRadio.setActionCommand("rectanglemap");
        viewAsRectangleMapRadio.addItemListener(new java.awt.event.ItemListener() {
            public void itemStateChanged(java.awt.event.ItemEvent evt) {
                viewAsItemChanged(evt);
            }
        });
        viewMenu.add(viewAsRectangleMapRadio);
        viewMenu.add(jSeparator1);

        multilineLabelsRadio.setText("Multiline Labels");
        multilineLabelsRadio.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                multilineLabelsPerformed(evt);
            }
        });
        viewMenu.add(multilineLabelsRadio);

        toolTipEnabledRadio.setSelected(true);
        toolTipEnabledRadio.setText("Show Tooltips");
        toolTipEnabledRadio.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                tooltipsEnabledPerformed(evt);
            }
        });
        viewMenu.add(toolTipEnabledRadio);

        jMenuBar1.add(viewMenu);

        helpMenu.setText("Help");

        aboutMenuItem.setText("About");
        aboutMenuItem.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                about(evt);
            }
        });
        helpMenu.add(aboutMenuItem);

        jMenuBar1.add(helpMenu);

        setJMenuBar(jMenuBar1);

        pack();
    }// </editor-fold>//GEN-END:initComponents
    private void openFile(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_openFile
        if (fileChooser == null) {
            fileChooser = new JFileChooser();
            if (prefs.get("file", null) != null) {
                fileChooser.setSelectedFile(new File(prefs.get("file", null)));
            }
            // fileChooser.setAcceptAllFileFilterUsed(false);
            // fileChooser.setFileFilter(new Exten)
            XMLFileAccessory acc = new XMLFileAccessory();
            acc.setFileChooser(fileChooser);
            fileChooser.setAccessory(acc);
        }
        if (JFileChooser.APPROVE_OPTION == fileChooser.showOpenDialog(this)) {
            prefs.put("file", fileChooser.getSelectedFile().toString());
            openFile(fileChooser.getSelectedFile());
        }
    }//GEN-LAST:event_openFile

    private void openFile(File file) {
        rootFile = file;
        new Worker<DemoTree>() {
            @Override
            public DemoTree construct() throws Exception {
                DemoTree tree;

                if (rootFile.getName().endsWith(".txt")) {
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
                setTitle("Tree Visualizer: " + info.getName(new TreePath2(rootNode)));
                treeView = null; // remove tree view
                updateView();
            }

            @Override
            public void failed(Throwable t) {
                String msg = t.getMessage();
                if (msg == null) {
                    msg = "";
                }
                if (t.getCause() != null && t.getCause().getMessage() != null) {

                    msg += "\n" + t.getCause().getMessage();
                }

                JOptionPane.showMessageDialog(Main.this, "Could not create tree structure.\n" + msg, "TreeViz", JOptionPane.ERROR_MESSAGE);
                t.printStackTrace();
            }
        }.start();
    }

    private void about(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_about
        FileSizeFormat byteFormat = FileSizeFormat.getInstance();

        JOptionPane.showMessageDialog(this, "<html>TreeViz " + Main.class.getPackage().getImplementationVersion() + "<br>"
                + "Copyright © 2007-2011<br>"
                + "Werner Randelshofer<br>"
                + "All rights reserved."
                + "<br><br>"
                + "Running on<br>"
                + System.getProperty("os.name") + " " + System.getProperty("os.version") + " "
                + System.getProperty("os.arch")
                + "<br>JavaVM "
                + System.getProperty("java.vm.version")
                + "<br>"
                + "<br>Memory "
                + "<br>  Max.: "
                + byteFormat.format(Runtime.getRuntime().maxMemory())
                + ", Usage: "
                + byteFormat.format(Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory()),
                "About", JOptionPane.PLAIN_MESSAGE);
    }//GEN-LAST:event_about

    private void viewAsItemChanged(java.awt.event.ItemEvent evt) {//GEN-FIRST:event_viewAsItemChanged
        String view = viewAsButtonGroup.getSelection().getActionCommand();

        if (view != null) {
            prefs.put("viewAs", view);
            updateView();
        }

    }//GEN-LAST:event_viewAsItemChanged

    private void openDirectory(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_openDirectory
        if (directoryChooser == null) {
            directoryChooser = new JFileChooser();
            directoryChooser.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
            if (prefs.get("directory", null) != null) {
                directoryChooser.setSelectedFile(new File(prefs.get("directory", null)));
            }
        }
        if (JFileChooser.APPROVE_OPTION == directoryChooser.showOpenDialog(this)) {
            prefs.put("directory", directoryChooser.getSelectedFile().toString());
            openDirectory(directoryChooser.getSelectedFile());
        }

    }//GEN-LAST:event_openDirectory

    private void tooltipsEnabledPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_tooltipsEnabledPerformed
        prefs.putBoolean("toolTipEnabled", toolTipEnabledRadio.isSelected());
        updateToolTipEnabled();
}//GEN-LAST:event_tooltipsEnabledPerformed

    private void maxDepthRadioPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_maxDepthRadioPerformed

        prefs.putInt("maxDepth", maxDepth1Radio.isSelected() ? 1 : Integer.MAX_VALUE);
        updateMaxDepth();

}//GEN-LAST:event_maxDepthRadioPerformed

    private void toggleHistogram(java.awt.event.MouseEvent evt) {//GEN-FIRST:event_toggleHistogram
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
    }//GEN-LAST:event_toggleHistogram

    private void multilineLabelsPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_multilineLabelsPerformed
        boolean isMultiline = multilineLabelsRadio.isSelected();


        prefs.putBoolean("multilineLabels", isMultiline);
        updateView();


    }//GEN-LAST:event_multilineLabelsPerformed

    private void printPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_printPerformed
        Paper paper = new Paper();
        paper.setSize(21/2.54*72, 29.7/2.54*72);
        paper.setImageableArea(1/2.54*72, 1/2.54*72, (21-2)/2.54*72, (29.7-2)/2.54*72);
        final PageFormat pageFormat = new PageFormat();
        pageFormat.setPaper(paper);

        Pageable pageable = new Pageable() {
            @Override
            public int getNumberOfPages() {
                return 1;
            }

            @Override
            public PageFormat getPageFormat(int pageIndex) throws IndexOutOfBoundsException {
                return pageFormat;
            }

            @Override
            public Printable getPrintable(int pageIndex) throws IndexOutOfBoundsException {
                return new Printable() {
                    @Override
                    public int print(Graphics graphics, PageFormat pageFormat, int pageIndex) throws PrinterException {
                        if (pageIndex != 0) {
                            return Printable.NO_SUCH_PAGE;
                        }
                        JComponent c=(JComponent)treeView;
                        Rectangle r=c.getBounds();
                        c.setBounds((int)pageFormat.getImageableX(),
                               (int) pageFormat.getImageableY(),
                               (int)pageFormat.getImageableWidth(),
                               (int)pageFormat.getImageableHeight());
                        treeView.repaintView();
                        graphics.translate((int)pageFormat.getImageableX(),
                               (int) pageFormat.getImageableY());
                        c.print(graphics);
                        graphics.translate(-(int)pageFormat.getImageableX(),
                               -(int) pageFormat.getImageableY());
                        c.setBounds(r);

                        return Printable.PAGE_EXISTS;
                    }
                };
            }
        };


        try {
            PrinterJob job = PrinterJob.getPrinterJob();
            // FIXME - PrintRequestAttributeSet should be retrieved from View
            PrintRequestAttributeSet attr = new HashPrintRequestAttributeSet();
            attr.add(new PrinterResolution(300, 300, PrinterResolution.DPI));
            job.setPageable(pageable);
            if (job.printDialog()) {
                try {
                    job.print();
                } catch (PrinterException e) {
                    String message = (e.getMessage() == null) ? e.toString() : e.getMessage();
                    JOptionPane.showMessageDialog(this,
                            "<html>" + UIManager.getString("OptionPane.css")
                            + "<b>" + "couldn't print" + "</b><br>"
                            + ((message == null) ? "" : message));
                }
            } else {
                System.out.println("JOB ABORTED!");
            }
        } catch (Throwable t) {
            t.printStackTrace();
        }
    }//GEN-LAST:event_printPerformed

    private void openDirectory(File dir) {
        rootNode = null;
        viewPanel.removeAll();
        treeView=null;
        repaint();
        rootFile = dir;
        new Worker() {
            @Override
            public Object construct() {

                FileNode root;
                /*if (rootFile.getParentFile() != null) {
                    root = new FileNode(rootFile.getParentFile(), rootFile);
                } else {
                    root = new FileNode(rootFile);
                }
                */
                    root = new FileNode(rootFile);
                return root;
            }

            @Override
            public void done(Object result) {
                rootNode = (FileNode) result;
                info = new FileNodeInfo();
                setTitle("Tree Visualizer: " + rootFile.getName());
                updateView();
            }
        }.start();
    }

    /**
     * Supports the following command line parameters:
     * <pre>
     * filename -weight weightAttribute -color colorAttribute
     * </pre>
     *
     * @param args the command line arguments
     */
    public static void main(final String args[]) {
        System.setProperty("apple.laf.useScreenMenuBar", "true");
        System.setProperty("com.apple.macos.useScreenMenuBar", "true");

        java.awt.EventQueue.invokeLater(new Runnable() {
            @Override
            public void run() {
                try {
                    UIManager.setLookAndFeel(UIManager.getSystemLookAndFeelClassName());
                } catch (Exception e) {
                    // UIManager does the right thing for us
                }

                ToolTipManager.sharedInstance().setDismissDelay(60000); // display tooltip for 10 minutes
                new Main().setVisible(true);
            }
        });
    }
    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JMenuItem aboutMenuItem;
    private javax.swing.JMenu fileMenu;
    private javax.swing.JMenu helpMenu;
    private ch.randelshofer.tree.demo.JHistogram histogram;
    private javax.swing.JMenuBar jMenuBar1;
    private javax.swing.JSeparator jSeparator1;
    private javax.swing.JRadioButton maxDepth1Radio;
    private javax.swing.ButtonGroup maxDepthButtonGroup;
    private javax.swing.JRadioButton maxDepthInfinityRadio;
    private javax.swing.JPanel maxDepthPanel;
    private javax.swing.JCheckBoxMenuItem multilineLabelsRadio;
    private javax.swing.JMenuItem openDirectoryMenuItem;
    private javax.swing.JMenuItem openFileMenuItem;
    private javax.swing.JMenuItem printMenuItem;
    private javax.swing.JPanel statusPanel;
    private javax.swing.JCheckBoxMenuItem toolTipEnabledRadio;
    private javax.swing.ButtonGroup viewAsButtonGroup;
    private javax.swing.JRadioButtonMenuItem viewAsCircleMapRadio;
    private javax.swing.JRadioButtonMenuItem viewAsHypertreeRadio;
    private javax.swing.JRadioButtonMenuItem viewAsIcerayRadio;
    private javax.swing.JRadioButtonMenuItem viewAsIcicleRadio;
    private javax.swing.JRadioButtonMenuItem viewAsRectangleMapRadio;
    private javax.swing.JRadioButtonMenuItem viewAsSunburstRadio;
    private javax.swing.JRadioButtonMenuItem viewAsSunrayRadio;
    private javax.swing.JMenu viewMenu;
    private javax.swing.JPanel viewPanel;
    // End of variables declaration//GEN-END:variables
}
