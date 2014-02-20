/**
 * @(#)RectmapView.java  1.3  2011-01-16
 *
 * Copyright (c) 2008-2001 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.rectmap;

import ch.randelshofer.gui.ProgressObserver;
import ch.randelshofer.gui.ProgressTracker;
import ch.randelshofer.tree.*;
import ch.randelshofer.util.Worker;
import ch.randelshofer.util.SequentialDispatcher;
import java.awt.*;
import java.awt.event.*;
import java.awt.geom.*;
import java.awt.image.*;
import javax.swing.*;
import javax.swing.event.*;
import static java.lang.Math.*;

/**
 * RectmapView provides an interactive user interface for a {@link RectmapTree}.
 * <p>
 * Supports zooming into a subtree.
 *
 * @author Werner Randelshofer
 * @version 1.3 2011-01-16 Adds popup menus.
 * <br>1.2 2008-10-22 Turn ToolTips off by default.
 * <br>1.1 2008-07-05 Draw asynchronously.
 * <br>1.0 RectmapView Created.
 */
public class RectmapView extends javax.swing.JPanel implements TreeView {

    private RectmapDraw draw;
    private BufferedImage img;
    private boolean isInvalid;
    private ProgressObserver workerProgress;
    private boolean drawHandles;
    private boolean isAdjusting;
    private boolean needsSimplify;
    private boolean needsProgressive = true;
    private RectmapNode hoverNode;
    private RectmapTree model;
    private SequentialDispatcher dispatcher = new SequentialDispatcher();
    private boolean isToolTipVisible = false;

    /** Creates new form. */
    public RectmapView() {
    }

    public RectmapView(RectmapTree model) {
        this.model = model;
        this.draw = createRectmapDraw(model);
        init();
        model.getInfo().addChangeListener(new ChangeListener() {

            @Override
            public void stateChanged(ChangeEvent e) {
                isInvalid = true;
                repaint();
            }
        });
    }

    public RectmapTree getModel() {
        return model;
    }
    public NodeInfo getInfo() {
        return model.getInfo();
    }

    
    
    protected RectmapDraw createRectmapDraw(RectmapTree model) {
        return new RectmapDraw(model);
    }
    public void setDraw(RectmapDraw newValue) {
        if (this.draw!=null&&newValue!=null) {
            newValue.setMaxDepth(this.draw.getMaxDepth());
        }
        this.draw=newValue;
        isInvalid=true;
    }
     
    private void init() {
        initComponents();
        MouseHandler handler = new MouseHandler();
        addMouseListener(handler);
        addMouseMotionListener(handler);
        ToolTipManager.sharedInstance().registerComponent(this);
        setFont(new Font("Dialog", Font.PLAIN, 9));
    }

    @Override
    public void setToolTipEnabled(boolean newValue) {
        isToolTipVisible = newValue;
    }

    @Override
    public boolean isToolTipEnabled() {
        return isToolTipVisible;
    }

    /**
     * Returns the tooltip to be displayed.
     *
     * @param event    the event triggering the tooltip
     * @return         the String to be displayed
     */
    @Override
    public String getToolTipText(MouseEvent event) {
        if (isToolTipVisible) {
            return getInfoText(event);
        } else {
            return null;
        }
    }

    /**
     * Returns the tooltip to be displayed.
     *
     * @param event    the event triggering the tooltip
     * @return         the String to be displayed
     */
    @Override
    public String getInfoText(MouseEvent event) {
        int x = event.getX();
        int y = event.getY();

        RectmapNode node = draw.getNodeAt(x, y);
        return (node == null) ? null : model.getInfo().getTooltip(node.getDataNodePath());
    }

    private void setDrawPosition(double cx, double cy) {
        draw.setX(cx);
        draw.setY(cy);
    }
    private void setDrawSize(double w, double h) {
        draw.setWidth(w);
        draw.setHeight(h);
    }
    private Rectangle2D.Double getDrawBounds() {
        return new Rectangle2D.Double(draw.getX(), draw.getY(), draw.getWidth(), draw.getHeight());
    }

    @Override
    public void repaintView() {
        isInvalid = true;
        repaint();
    }

    @Override
    public void paintComponent(Graphics gr) {
        int w = getWidth();
        int h = getHeight();
        setDrawPosition(2, 2);
        setDrawSize(w - 4, h - 4);

        if (img == null
                || img.getWidth() != w
                || img.getHeight() != h) {
            img = null;
            img = new BufferedImage(w, h, BufferedImage.TYPE_INT_RGB);
            Graphics2D g = img.createGraphics();
            g.setBackground(Color.WHITE);
            g.clearRect(0, 0, img.getWidth(), img.getHeight());
            g.dispose();
            isInvalid = true;
        }
        if (isInvalid) {
            if (workerProgress != null) {
                workerProgress.cancel();
            } else {
                isInvalid = false;
                final BufferedImage workingImage = img;
                workerProgress = new ProgressTracker("Rectangular Treemap", "Drawing...");
                workerProgress.setIndeterminate(true);
                final Timer timer = new Timer(33, new ActionListener() {

                    @Override
                    public void actionPerformed(ActionEvent e) {
                        repaint();
                    }
                });
                timer.isRepeats();
                timer.start();
                final Worker worker = new Worker() {

                    @Override
                    public Object construct() {
                        Graphics2D g = workingImage.createGraphics();
                        g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
                        g.setBackground(Color.WHITE);
                        g.setFont(getFont());
                        g.clearRect(0, 0, workingImage.getWidth(), workingImage.getHeight());
                        g.setClip(new Rectangle(0, 0, workingImage.getWidth(), workingImage.getHeight()));
                        if (isAdjusting && needsSimplify) {
                            //  draw.drawContours(g, draw.getRoot(), Color.gray);
                            draw.drawTree(g, workerProgress);
                        } else {
                            long start = System.currentTimeMillis();
                            draw.drawTree(g, workerProgress);
                            long end = System.currentTimeMillis();
                            needsSimplify = (end - start) > 99;
                            needsProgressive = (end - start) > 33;
                        }

                        g.dispose();
                        return null;
                    }

                    @Override
                    public void done(Object value) {
                        workerProgress.close();
                        workerProgress = null;
                        repaint();
                        timer.stop();
                    }
                };

                //if (!isAdjusting && !needsSimplify && needsProgressive) {
                //   dispatcher.dispatch(worker);
                /*} else {
                worker.done(worker.construct());
                }*/

                if (needsProgressive) {
                    dispatcher.dispatch(worker);
                } else {
                    worker.run();
                }
            }

        }


        gr.drawImage(img, 0, 0, this);
        RectmapNode selectedNode = draw.getDrawRoot();
        if (selectedNode != null) {
            Graphics2D g = (Graphics2D) gr;
            g.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
                    RenderingHints.VALUE_ANTIALIAS_ON);
            // draw.drawNodeBounds(g, selectedNode, Color.blue);
        }
        if (hoverNode != null) {
            Graphics2D g = (Graphics2D) gr;
            g.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
                    RenderingHints.VALUE_ANTIALIAS_ON);
            RectmapNode node = hoverNode;
            while ((node = node.getParent()) != null) {
                draw.drawNodeBounds(g, node, Color.blue);
            }
            draw.drawNodeBounds(g, hoverNode, Color.red);
        }

        if (drawHandles) {
            Graphics2D g = (Graphics2D) gr;
            double cx = draw.getX();
            double cy = draw.getY();
            g.setColor(Color.BLACK);
            AffineTransform t = new AffineTransform();
            t.translate(cx, cy);
            //  t.rotate(draw.getRotation() * Math.PI / -180d);
            AffineTransform oldT = (AffineTransform) g.getTransform().clone();
            g.setTransform(t);
            g.draw(new Line2D.Double(-5, 0, 5, 0));
            g.draw(new Line2D.Double(0, -5, 0, 5));
            g.setTransform(oldT);
        }

    }
    @Override
    public void printComponent(Graphics gr) {
        int w = getWidth();
        int h = getHeight();

        Rectangle2D.Double savedBounds=getDrawBounds();
        
        setDrawPosition(2, 2);
        setDrawSize(min(w - 4,h-4),min(w-4, h - 4));
        
        
        Graphics2D g = (Graphics2D) gr;
        g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
        g.setFont(getFont());
        try {
        draw.drawTree(g, new ProgressTracker("Circular Treemap", "Printing..."));
        } catch (Throwable t) {t.printStackTrace();}
        RectmapNode selectedNode = draw.getDrawRoot();
  if (selectedNode != null) {
            g.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
                    RenderingHints.VALUE_ANTIALIAS_ON);
             draw.drawNodeBounds(g, selectedNode, Color.blue);
        }        
        setDrawPosition(savedBounds.x,savedBounds.y);
        setDrawSize(savedBounds.width,savedBounds.height);
    }
    @Override
    public void setMaxDepth(int newValue) {
        if (newValue != draw.getMaxDepth()) {
            draw.setMaxDepth(newValue);
            isInvalid = true;
            if (newValue == Integer.MAX_VALUE) {
                needsProgressive = true;
            }
            repaint();
        }
    }

    @Override
    public int getMaxDepth() {
        return draw.getMaxDepth();
    }

    private class MouseHandler implements MouseListener, MouseMotionListener {

        @Override
        public void mouseClicked(MouseEvent evt) {
            if (evt.getButton() == MouseEvent.BUTTON1) {
                RectmapNode node = draw.getNodeAt(evt.getX(), evt.getY());
                if (node == draw.getDrawRoot()) {
                    node = draw.getRoot();
                }
                if (node != draw.getDrawRoot()) {
                    draw.setDrawRoot((node == null || node == draw.getDrawRoot()) ? draw.getRoot() : node);

                    isInvalid = true;
                    repaint();
                }
            }
        }

        @Override
        public void mousePressed(MouseEvent e) {
            if (e.isPopupTrigger()) {
                showPopup(e);
            }
        }

        @Override
        public void mouseReleased(MouseEvent e) {
            if (e.isPopupTrigger()) {
                showPopup(e);
            }
        }

        @Override
        public void mouseEntered(MouseEvent evt) {
            hoverNode = draw.getNodeAt(evt.getX(), evt.getY());
            repaint();
        }

        @Override
        public void mouseExited(MouseEvent e) {
            hoverNode = null;
            repaint();
        }

        @Override
        public void mouseDragged(MouseEvent e) {
        }

        @Override
        public void mouseMoved(MouseEvent evt) {
            hoverNode = draw.getNodeAt(evt.getX(), evt.getY());
            repaint();
        }

        private void showPopup(MouseEvent evt) {
            RectmapNode popupNode = draw.getNodeAt(evt.getX(), evt.getY());
            if (popupNode != null) {
                TreePath2 treePath = popupNode.getDataNodePath();
                Action[] a = model.getInfo().getActions(treePath);
                if (a.length > 0) {
                    JPopupMenu m = new JPopupMenu();
                    for (int i = 0; i < a.length; i++) {
                        m.add(a[i]);
                    }
                    m.show(RectmapView.this, evt.getX(), evt.getY());
                }
            }
            evt.consume();
        }
    }

    /** This method is called from within the constructor to
     * initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is
     * always regenerated by the Form Editor.
     */
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        setLayout(new java.awt.BorderLayout());
    }// </editor-fold>//GEN-END:initComponents
    // Variables declaration - do not modify//GEN-BEGIN:variables
    // End of variables declaration//GEN-END:variables
}
