/*
 * @(#)SwingSBView.java  1.3  2011-01-16
 *
 * Copyright (c) 2007-2011 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.sunburst;

import ch.randelshofer.tree.NodeInfo;
import ch.randelshofer.tree.TreePath2;
import ch.randelshofer.tree.TreeView;
import java.awt.*;
import java.awt.event.*;
import java.awt.geom.*;
import java.awt.image.*;
import javax.swing.*;

/**
 * IcicleView provides an interactive user interface for an {@link IcicleTree}.
 * <p>
 * Supports zooming into a subtree.
 *
 * @author Werner Randelshofer
 * @version 1.3 2011-01-16 Adds popup menus.
 * <br>1.0 September 18, 2007 Created.
 */
public class IcicleView extends JPanel implements SunburstViewer, TreeView {

    private IcicleDraw draw;
    private IcicleDraw subDraw;
    private BufferedImage img;
    private boolean isInvalid;
    private boolean drawHandles;
    private boolean isAdjusting;
    private boolean needsSimplify;
    private boolean isToolTipVisible = false;
    /**
     * The selected node of the sunburst tree. Can be null.
     */
    private SunburstNode selectedNode;
    /**
     * The node under the mouse cursor. Can be null.
     */
    private SunburstNode hoverNode;
    private SunburstTree model;

    /** Creates new instance. */
    public IcicleView() {
        init();
    }

    public IcicleView(SunburstTree model) {
        this.draw = new IcicleDraw(model);
        this.model = model;
        init();
    }

    protected IcicleDraw createSubDraw(SunburstNode root, NodeInfo info) {
        if (draw instanceof MultilineIcicleDraw) {
            return new MultilineIcicleDraw(root, info);
        } else {
            return new IcicleDraw(root, info);
        }
    }
    
    private void init() {
        initComponents();
        MouseHandler handler = new MouseHandler();
        addMouseListener(handler);
        addMouseMotionListener(handler);
        ToolTipManager.sharedInstance().registerComponent(this);
            setFont(new Font("Dialog", Font.PLAIN, 9));
    }
    public void setDraw(IcicleDraw newValue) {
        this.draw=newValue;
        this.selectedNode=null;
        this.subDraw=null;
        setTreeBounds(4, 4, getWidth() - 8, getHeight() - 8);
        isInvalid=true;
    }

    public void setTreeLocation(double x, double y) {
        draw.setX(x);
        draw.setY(y);
        subDraw.setX(x + draw.getWidth() + draw.getWidth() / draw.getTotalDepth());
        subDraw.setY(y);
    }
    
    public Rectangle2D.Double getTreeBounds() {
        if (subDraw==null)
            return new Rectangle2D.Double(draw.getX(),draw.getY(),draw.getWidth(),draw.getHeight());
        else {
            Rectangle2D.Double r1= new Rectangle2D.Double(draw.getX(),draw.getY(),draw.getWidth(),draw.getHeight());
            Rectangle2D.Double r2= new Rectangle2D.Double(subDraw.getX(),subDraw.getY(),subDraw.getWidth(),subDraw.getHeight());
             r1.add(r2);
             return r1;
        }
    }

    public void setTreeBounds(double x, double y, double width, double height) {
        if (subDraw == null) {
            draw.setX(x);
            draw.setY(y);
            draw.setWidth(width);
            draw.setHeight(height);
        } else {
            draw.setX(x);
            draw.setY(y);
            draw.setWidth(width / 2 - (width / 2) / draw.getTotalDepth());
            draw.setHeight(height);
            if (subDraw.getRoot().isLeaf()) {
                subDraw.setX(x + width / 2);
                subDraw.setWidth(width / 2);
            } else {
                subDraw.setX(x + width / 2 - (width / 2 / (subDraw.getTotalDepth() - 1)));
                subDraw.setWidth(width / 2 + (width / 2 / (subDraw.getTotalDepth() - 1)));
            }
            subDraw.setY(y);
            subDraw.setHeight(height);
        }
    }

    @Override
    public void setMaxDepth(int newValue) {
        //throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public int getMaxDepth() {
        return Integer.MAX_VALUE;
        // throw new UnsupportedOperationException("Not supported yet.");
    }

    public SunburstTree getModel() {
        return model;
    }

    private class MouseHandler implements MouseListener, MouseMotionListener {

        private double alphaStart;
        private boolean isMove;
        private Point moveStart;

        @Override
        public void mouseClicked(MouseEvent evt) {
            SunburstNode node = draw.getNodeAt(evt.getX(), evt.getY());
            if (node == null && subDraw != null) {
                node = subDraw.getNodeAt(evt.getX(), evt.getY());
                if (node == subDraw.getRoot() && !subDraw.getRoot().children().isEmpty()) {
                    node = null;
                }
            }
            if (node == draw.getRoot()) {
                setSelectedNode(null);
                if (evt.getClickCount() == 2) {
                    setTreeBounds(4, 4, getWidth() - 8, getHeight() - 8);
                    setSelectedNode(null);
                }
            } else {
                setSelectedNode(node);
            }
            isInvalid = true;
            repaint();
        }

        @Override
        public void mousePressed(MouseEvent e) {
            if (e.isPopupTrigger()) {
                showPopup(e);
            } else {
                isMove = draw.getNodeAt(e.getX(), e.getY()) == draw.getRoot();
                moveStart = e.getPoint();
                alphaStart = draw.getTheta(e.getX(), e.getY());
            }
        }

        @Override
        public void mouseReleased(MouseEvent e) {
            if (e.isPopupTrigger()) {
                showPopup(e);
            } else {
                if (drawHandles || isAdjusting) {
                    drawHandles = false;
                    if (isAdjusting) {
                        isAdjusting = false;
                        isInvalid = true;
                    }
                    repaint();
                }
            }
        }

        @Override
        public void mouseEntered(MouseEvent e) {
        }

        @Override
        public void mouseExited(MouseEvent e) {
            if (drawHandles) {
                drawHandles = false;
                repaint();
            }
        }

        @Override
        public void mouseDragged(MouseEvent e) {
            isAdjusting = true;
            if (isMove) {
                Point moveNow = e.getPoint();
                int cx = (int) draw.getX();
                int cy = (int) draw.getY();
                setTreeLocation(cx + moveNow.x - moveStart.x,
                        cy + moveNow.y - moveStart.y);
                moveStart = moveNow;
                isInvalid = true;
                repaint();
            } else {
                double alphaNow = draw.getTheta(e.getX(), e.getY());

                isInvalid = true;
                repaint();
            }
        }

        @Override
        public void mouseMoved(MouseEvent e) {
            hoverNode = draw.getNodeAt(e.getX(), e.getY());
            if (hoverNode == null && subDraw != null) {
                hoverNode = subDraw.getNodeAt(e.getX(), e.getY());
                if (hoverNode == subDraw.getRoot()
                        && !subDraw.getRoot().children().isEmpty()) {
                    hoverNode = null;
                }
            }
            //isInvalid = true;
            repaint();
            /*
            boolean b = draw.getNodeAt(e.getX(), e.getY()) == draw.getRoot();
            if (b != drawHandles) {
            drawHandles = b;
            repaint();
            }*/
        }

        private void showPopup(MouseEvent evt) {
            SunburstNode popupNode = draw.getNodeAt(evt.getX(), evt.getY());
            if (popupNode != null) {
                TreePath2 treePath = popupNode.getDataNodePath();
                Action[] a = model.getInfo().getActions(treePath);
                if (a.length > 0) {
                    JPopupMenu m = new JPopupMenu();
                    for (int i = 0; i < a.length; i++) {
                        m.add(a[i]);
                    }
                    m.show(IcicleView.this, evt.getX(), evt.getY());
                }
            }
            evt.consume();
        }
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

        if (img == null
                || img.getWidth() != w
                || img.getHeight() != h) {
            if (img == null) {
                setTreeBounds(4, 4, getWidth() - 8, getHeight() - 8);
            } else {
                setTreeBounds(4, 4, getWidth() - 8, getHeight() - 8);
            }
            img = null;
            img = new BufferedImage(w, h, BufferedImage.TYPE_INT_RGB);
            isInvalid = true;
        }
        if (isInvalid) {
            isInvalid = false;
            Graphics2D g = img.createGraphics();
            g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
            g.setBackground(Color.WHITE);
            g.setFont(getFont());
            g.clearRect(0, 0, img.getWidth(), img.getHeight());
            if (isAdjusting && needsSimplify) {
                draw.drawContours(g, draw.getRoot(), Color.gray);
                if (subDraw != null) {
                    subDraw.drawContours(g, subDraw.getRoot(), Color.gray);
                }
            } else {
                long start = System.currentTimeMillis();
                draw.drawTree(g);
                if (subDraw != null) {
                    if (subDraw.getRoot().children().isEmpty()) {
                        subDraw.drawTree(g);
                    } else {
                        subDraw.drawDescendants(g, subDraw.getRoot());
                    }
                }
                long end = System.currentTimeMillis();
                needsSimplify = (end - start) > 500;
            }

            g.dispose();
        }



        gr.drawImage(img, 0, 0, this);

        if (selectedNode != null) {
            Graphics2D g = (Graphics2D) gr;
            g.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
                    RenderingHints.VALUE_ANTIALIAS_ON);
            if (selectedNode.children().isEmpty()) {
                draw.drawSubtreeBounds(g, selectedNode, Color.red);
            } else {
                draw.drawDescendantSubtreeBounds(g, selectedNode, Color.red);
            }
        }
        if (hoverNode != null) {
            Graphics2D g = (Graphics2D) gr;
            g.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
                    RenderingHints.VALUE_ANTIALIAS_ON);
            draw.drawNodeBounds(g, hoverNode, Color.black);
            if (subDraw != null && subDraw.getRoot().isDescendant(hoverNode)) {
                if (hoverNode != subDraw.getRoot() || subDraw.getRoot().children().isEmpty()) {
                    subDraw.drawNodeBounds(g, hoverNode, Color.BLACK);
                }
            }
        }

        if (drawHandles) {
            Graphics2D g = (Graphics2D) gr;
            double cx = draw.getX();
            double cy = draw.getY();
            g.setColor(Color.BLACK);
            AffineTransform t = new AffineTransform();
            t.translate(cx, cy);
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
        
        Rectangle2D.Double savedBounds=getTreeBounds();

            Graphics2D g = (Graphics2D) gr;
            g.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
            
                setTreeBounds(4, 4, w - 8, h - 8);

                draw.drawTree(g);
                if (subDraw != null) {
                    if (subDraw.getRoot().children().isEmpty()) {
                        subDraw.drawTree(g);
                    } else {
                        subDraw.drawDescendants(g, subDraw.getRoot());
                    }
                }
                long end = System.currentTimeMillis();

        if (selectedNode != null) {
            g.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
                    RenderingHints.VALUE_ANTIALIAS_ON);
            if (selectedNode.children().isEmpty()) {
                draw.drawSubtreeBounds(g, selectedNode, Color.red);
            } else {
                draw.drawDescendantSubtreeBounds(g, selectedNode, Color.red);
            }
        }
        
        setTreeBounds(savedBounds.x,savedBounds.y,savedBounds.width,savedBounds.height);
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

        SunburstNode node = draw.getNodeAt(x, y);
        if (node == null && subDraw != null) {
            node = subDraw.getNodeAt(x, y);
            if (node == subDraw.getRoot() && !subDraw.getRoot().children().isEmpty()) {
                node = null;
            }
        }
        return (node == null) ? null : model.getInfo().getTooltip(node.getDataNodePath());
    }

    public void setSelectedNode(SunburstNode newValue) {
        selectedNode = newValue;
        if (selectedNode == null) {
            if (subDraw != null) {
                draw.setWidth(subDraw.getX() + subDraw.getWidth() - draw.getX());
                subDraw = null;
            }
        } else {
            if (selectedNode.children().isEmpty()) {
                subDraw = createSubDraw(selectedNode, draw.getInfo());
            } else {
                subDraw = createSubDraw(selectedNode, draw.getInfo());
            }
            setTreeBounds(4, 4, getWidth() - 8, getHeight() - 8);
        }
    }

    /** This method is called from within the constructor to
     * initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is
     * always regenerated by the Form Editor.
     */
    // <editor-fold defaultstate="collapsed" desc=" Generated Code ">//GEN-BEGIN:initComponents
    private void initComponents() {

        setLayout(new java.awt.BorderLayout());

    }// </editor-fold>//GEN-END:initComponents
    // Variables declaration - do not modify//GEN-BEGIN:variables
    // End of variables declaration//GEN-END:variables
}
