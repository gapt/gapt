/**
 * @(#)RectmapDraw.java  1.2  2009-01-30
 *
 * Copyright (c) 2008 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.rectmap;

import ch.randelshofer.gui.ProgressObserver;
import ch.randelshofer.tree.NodeInfo;
import java.awt.*;
import java.awt.geom.*;

/**
 * RectmapDraw draws a {@link RectmapTree}.
 * <p>
 * Can draw a subtree from any node within the tree.
 *
 * @author Werner Randelshofer
 * @version 1.2 2009-01-30 Added maxDepth property.
 * <br>1.1 2008-07-04 Draw asynchronously.
 * <br>1.0 Jan 16, 2008 Created.
 */
public class RectmapDraw {

    private RectmapNode root;
    private RectmapNode drawRoot;
    protected NodeInfo info;
    private Insets insets = new Insets(10, 10, 10, 10);
    /**
     * Top left corner of the draw root.
     */
    protected double cx = 2,  cy = 2;
    /**
     * Width and height of the draw root.
     */
    private double cwidth = 96;
    private double cheight = 96;
    private double scaleFactorH = 1;
    private double scaleFactorV = 1;
    /** Maximal depth of the tree that will be drawn, starting from
     * the draw root. */
    protected int maxDepth = Integer.MAX_VALUE;

    public RectmapDraw(RectmapTree model) {
        this(model.getRoot(), model.getInfo());
    }

    public RectmapDraw(RectmapNode root, NodeInfo info) {
        this.root = root;
        this.drawRoot = root;
        this.info = info;
        setMaxDepth(1);
    }

    public double getX() {
        return cx;
    }

    public void setX(double newValue) {
        cx = newValue;
    }

    public int getMaxDepth() {
        return maxDepth;
    }

    public void setMaxDepth(int newValue) {
        maxDepth = newValue;
    }

    public double getY() {
        return cy;
    }

    public void setY(double newValue) {
        cy = newValue;
    }

    public double getWidth() {
        return cwidth;
    }

    public void setWidth(double newValue) {
        cwidth = newValue;
    }

    public double getHeight() {
        return cheight;
    }

    public void setHeight(double newValue) {
        cheight = newValue;
    }

    /**
     * Draws the tree onto
     * the supplied graphics object.
     */
    public void drawTree(Graphics2D g, ProgressObserver p) {
        scaleFactorH = (cwidth - insets.left - insets.right) / drawRoot.getWidth();
        scaleFactorV = (cheight - insets.top - insets.bottom) / drawRoot.getHeight();
        double sx = 0;
        double sy = 0;
        RectmapNode node = drawRoot;
        int depth = 1;
        while (node != null) {
            sx -= node.getX();
            sy -= node.getY();
            node = node.getParent();
            depth--;
        }
        drawTree0(g, root, depth, sx + insets.left / scaleFactorH, sy + insets.top / scaleFactorV, scaleFactorH, scaleFactorV, p);
    }

    /**
     * Recursive part of the drawing routine.
     */
    public void drawTree0(Graphics2D g, RectmapNode node, int depth, double px, double py, double pwidth, double pheight, ProgressObserver p) {
        if (!p.isCanceled()) {
            drawNode(g, node, depth, px, py, pwidth, pheight);
            drawLabel(g, node, depth, px, py, pwidth, pheight);

            Rectangle2D.Double rect = new Rectangle2D.Double(
                    (px) * pwidth + cx, (py) * pheight + cy,
                    node.width * pwidth, node.height * pheight);
            if (depth < maxDepth &&
                    rect.width > 1 && rect.height > 1 && (g.getClipBounds() == null ||
                    g.getClipBounds().intersects(rect))) {
                for (RectmapNode child : node.children()) {
                    drawTree0(g, child, depth + 1,
                            px + child.getX(),
                            py + child.getY(),
                            pwidth, pheight, p);
                }
            }
        }
    }

    public void drawNode(Graphics2D g, RectmapNode node, int depth, double px, double py, double sfh, double sfv) {
        Rectangle2D.Double rect = new Rectangle2D.Double(
                (px) * sfh + cx, (py) * sfv + cy,
                node.width * sfh, node.height * sfv);

        rect.x += 1;
        rect.width -= 2;
        rect.y += 1;
        rect.height -= 2;

        if (rect.width > 0 && rect.height > 0) {
            Color c = info.getColor(node.getDataNodePath());
            g.setColor(c);
            g.fill(rect);
            g.setColor(c.brighter());
            g.draw(new Line2D.Double(rect.x, rect.y, rect.x + rect.width - 1, rect.y));
            g.draw(new Line2D.Double(rect.x, rect.y, rect.x, rect.y + rect.height - 1));
            g.setColor(c.darker());
            g.draw(new Line2D.Double(rect.x, rect.y + rect.height - 1, rect.x + rect.width - 1, rect.y + rect.height - 1));
            g.draw(new Line2D.Double(rect.x + rect.width - 1, rect.y, rect.x + rect.width - 1, rect.y + rect.height - 1));
        }
    }

    public void drawLabel(Graphics2D g, RectmapNode node, int depth, double px, double py, double sfh, double sfv) {
        if (node.children().size() == 0 || depth == maxDepth) {
            Rectangle2D.Double rect = new Rectangle2D.Double(
                    (px) * sfh + cx, (py) * sfv + cy,
                    node.width * sfh, node.height * sfv);

            FontMetrics fm = g.getFontMetrics();
            int fh = fm.getHeight();
            if (fh < rect.height) {
                g.setColor(Color.BLACK);
                double space = rect.width - 6;

                int y = (int) (rect.y + (rect.height - fh) / 2) + fm.getAscent();

                // Draw the weight only, if it fully fits into the rectangle
                if (fh * 2 < rect.height) {
                    String weightStr = info.getWeightFormatted(node.getDataNodePath());
                    int weightWidth = fm.stringWidth(weightStr);
                    if (weightWidth < space) {
                        g.drawString(weightStr,
                                (int) (rect.x + (rect.width - weightWidth) / 2),
                                y + fh / 2);
                        y -= fh / 2;
                    }
                }


                String name;
                char[] nameC;
                int nameLength;
                int nameWidth;


                if (node.children().size() == 0) {
                // Label for node without children ends with a mid-dot, if
                // the name is too long
                    name = info.getName(node.getDataNodePath());
                    nameC = name.toCharArray();
                    nameLength = nameC.length;
                    nameWidth = fm.charsWidth(nameC, 0, nameLength);


                    while ((nameWidth >= space) && (nameLength > 1)) {
                        nameLength--;
                        nameC[nameLength - 1] = '·';
                        nameWidth = fm.charsWidth(nameC, 0, nameLength);
                    }
                } else {
                // Label for node with children allways ands with >,
                    // regardless. So that it is clear, that we pruned
                    // the tree here.
                    name = info.getName(node.getDataNodePath())+"›";
                    nameC = name.toCharArray();
                    nameLength = nameC.length;
                    nameWidth = fm.charsWidth(nameC, 0, nameLength);


                    while ((nameWidth >= space) && (nameLength > 1)) {
                        nameLength--;
                        nameC[nameLength - 1] = '›';
                        nameWidth = fm.charsWidth(nameC, 0, nameLength);
                    }
                }

                if (nameLength > 1 || nameLength == nameC.length) {
                    g.drawString(new String(nameC, 0, nameLength),
                            (int) (rect.x + (rect.width - nameWidth) / 2),
                            y);
                }

            }
        }
    }

    public void drawContours(Graphics2D g, RectmapNode node, Color color) {
    }

    public NodeInfo getInfo() {
        return info;
    }

    public RectmapNode getRoot() {
        return root;
    }

    public RectmapNode getDrawRoot() {
        return drawRoot;
    }

    public void setDrawRoot(RectmapNode newValue) {
        this.drawRoot = newValue;
    }

    public void drawNodeBounds(Graphics2D g, RectmapNode selectedNode, Color color) {
        g.setColor(color);
        double scx = 0;
        double scy = 0;

        RectmapNode node = selectedNode;
        while (node != null) {
            scx += node.getX();
            scy += node.getY();
            node = node.getParent();
        }
        node = drawRoot;
        while (node != null) {
            scx -= node.getX();
            scy -= node.getY();
            node = node.getParent();
        }

        double px = scx * scaleFactorH + cx + insets.left;
        double py = scy * scaleFactorV + cy + insets.top;

        Rectangle.Double rect = new Rectangle2D.Double(px, py,
                selectedNode.width * scaleFactorH - 2,
                selectedNode.height * scaleFactorV - 2);
        g.draw(rect);
    }

    /**
     * Returns the node at the specified view coordinates.
     * @param px
     * @param py
     * @return
     */
    public RectmapNode getNodeAt(int px, int py) {
        return getNodeAt((px - cx - insets.left) / scaleFactorH, (py - cy - insets.top) / scaleFactorV);
    }

    /**
     * Returns the node at the specified draw coordinates.
     */
    public RectmapNode getNodeAt(double px, double py) {
        RectmapNode parent = drawRoot;
        int depth = 1;
        while (parent != null) {
            px += parent.getX();
            py += parent.getY();
            parent = parent.getParent();
            depth--;
        }

        Rectangle2D.Double slimmed = new Rectangle2D.Double();
        if (root.contains(px, py)) {
            RectmapNode found = root;
            parent = found;
            do {
                parent = found;
                px -= parent.x;
                py -= parent.y;
                for (RectmapNode node : parent.children()) {
                    slimmed.setRect(node.x + (1 / scaleFactorH), node.y + (1 / scaleFactorV),
                            node.width - (2 / scaleFactorH), node.height - (2 / scaleFactorV));
//                    slimmed.setRect(node.x, node.y, node.pwidth, node.pheight);
                    if (slimmed.contains(px, py)) {
                        found = node;
                        depth++;
                        break;
                    }
                }
            } while (found != parent && depth < maxDepth);
            return found;
        } else {
            return null;
        }
    }
}
