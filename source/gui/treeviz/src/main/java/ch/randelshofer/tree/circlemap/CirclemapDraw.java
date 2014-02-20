/**
 * @(#)CirclemapDraw.java  1.2  2009-02-04
 *
 * Copyright (c) 2008-2009 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.circlemap;

import ch.randelshofer.gui.ProgressObserver;
import ch.randelshofer.tree.NodeInfo;
import java.awt.*;
import java.awt.geom.*;
import java.util.ArrayList;

/**
 * CirclemapDraw draws a {@link CirclemapTree}.
 * <p>
 * Can draw a subtree from any node within the tree.
 *
 * @author Werner Randelshofer
 * @version 1.2 2009-02-04 If we prune on the depth of the tree, fill the
 * composite node only by an amount which visualizes its weight.
 * <br>1.1 2009-01-30 Added maxDepth property.
 * <br>1.0 Jan 16, 2008 Created.
 */
public class CirclemapDraw {

    private CirclemapNode root;
    private CirclemapNode drawRoot;
    private NodeInfo info;
    /**
     * Center of the tree.
     */
    private double cx = 100,  cy = 100;
    /**
     * Radius of the phyllotactic tree.
     */
    private double radius = 96;
    private double scaleFactor = 1;
    private int maxDepth = Integer.MAX_VALUE;

    public CirclemapDraw(CirclemapTree model) {
        this(model.getRoot(), model.getInfo());
    }

    public CirclemapDraw(CirclemapNode root, NodeInfo info) {
        this.root = root;
        this.drawRoot = this.root;
        this.info = info;
    }

    public double getCX() {
        return cx;
    }

    public void setCX(double newValue) {
        cx = newValue;
    }

    public double getCY() {
        return cy;
    }

    public void setCY(double newValue) {
        cy = newValue;
    }

    public double getRadius() {
        return radius;
    }

    public void setRadius(double newValue) {
        radius = newValue;
    }

    /**
     * Draws the tree onto
     * the supplied graphics object.
     */
    public void drawTree(Graphics2D g, ProgressObserver p) {
        scaleFactor = radius / drawRoot.getRadius();
        double sx = 0;
        double sy = 0;
        CirclemapNode node = drawRoot;
        int depth = 1;
        while (node != null) {
            sx -= node.getCX();
            sy -= node.getCY();
            node = node.getParent();
            depth--;
        }

        Rectangle clipBounds = g.getClipBounds();
        if (clipBounds == null) {
            clipBounds = new Rectangle(0, 0, Integer.MAX_VALUE, Integer.MAX_VALUE);
        }
        drawTree0(g, root, depth, sx, sy, scaleFactor, clipBounds, p);
    }

    public void drawTree0(Graphics2D g, CirclemapNode node, int depth, double px, double py, double sf, Rectangle clipBounds, ProgressObserver p) {
        if (!p.isCanceled()) {
            drawNode(g, node, depth, px, py, sf);
            drawLabel(g, node, depth, px, py, sf);

            if (node.radius * sf > 1 && node.children().size() > 0) {
                double r = node.getRadius() * sf;
                Rectangle2D.Double bounds = new Rectangle2D.Double(
                        cx + sf * px - r,
                        cy + sf * py - r, r * 2, r * 2);
                if (depth < maxDepth && clipBounds.intersects(bounds)) {
                    for (CirclemapNode child : node.children()) {
                        drawTree0(g, child, depth + 1,
                                px + child.getCX(),
                                py + child.getCY(),
                                sf, clipBounds, p);
                    }
                }
            }
        }
    }
    public void drawNode(Graphics2D g, CirclemapNode node, int depth, double px, double py, double sf) {
        double r = node.getRadius() * sf;
        Ellipse2D.Double ellipse = new Ellipse2D.Double(
                cx + sf * px - r,
                cy + sf * py - r,
                r * 2, r * 2);

        if (node.isLeaf()) {
            g.setColor(info.getColor(node.getDataNodePath()));
            g.fill(ellipse);
            g.setColor(info.getColor(node.getDataNodePath()).darker());
            g.draw(ellipse);
        } else if (depth == maxDepth) {
            double r2 = node.getWeightRadius(info) * sf;
            ellipse.x = cx + sf * px - r2;
            ellipse.y = cy + sf * py - r2;
            ellipse.width = ellipse.height = r2 * 2;
            g.setColor(info.getColor(node.getDataNodePath()));
            g.fill(ellipse);
            g.setColor(info.getColor(node.getDataNodePath()).darker());
            g.draw(ellipse);
        } else {
            g.setColor(info.getColor(node.getDataNodePath()).darker());
            g.draw(ellipse);
        }
    }


    public void drawLabel(Graphics2D g, CirclemapNode node, int depth, double px, double py, double sf) {
        if (node.children().size() == 0 || depth == maxDepth) {
            double r;
            if (depth == maxDepth) {
                r = node.getWeightRadius(info) * sf;
            } else {
                r = node.getRadius() * sf;
            }
            Ellipse2D.Double ellipse = new Ellipse2D.Double(
                    cx + sf * px - r,
                    cy + sf * py - r,
                    r * 2, r * 2);
            FontMetrics fm = g.getFontMetrics();
            int fh = fm.getHeight();
            if (fh < ellipse.height) {
                g.setColor(Color.BLACK);

                double space = ellipse.width - 6;

                int y = (int) (ellipse.y + (ellipse.height - fh) / 2) + fm.getAscent();

                // Draw the weight only, if it fully fits into the rectangle
                if (fh * 2 < ellipse.height) {
                    String weightStr = info.getWeightFormatted(node.getDataNodePath());
                    int weightWidth = fm.stringWidth(weightStr);
                    if (weightWidth < space) {
                        g.drawString(weightStr,
                                (int) (ellipse.x + (ellipse.width - weightWidth) / 2),
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
                    name = info.getName(node.getDataNodePath()) + "›";
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
                            (int) (ellipse.x + (ellipse.width - nameWidth) / 2),
                            y);
                }
            }
        }
    }

    public void drawContours(Graphics2D g, CirclemapNode node, Color color) {
    }

    public NodeInfo getInfo() {
        return info;
    }

    public CirclemapNode getRoot() {
        return root;
    }

    public CirclemapNode getDrawRoot() {
        return drawRoot;
    }

    public void setDrawRoot(CirclemapNode newValue) {
        this.drawRoot = newValue;
    }

    public void drawNodeBounds(Graphics2D g, CirclemapNode selectedNode, Color color) {
        g.setColor(color);
        double r = selectedNode.getRadius() * scaleFactor;
        double scx = 0;
        double scy = 0;

        CirclemapNode node = selectedNode;
        while (node != null) {
            scx += node.getCX();
            scy += node.getCY();
            node = node.getParent();
        }
        node = drawRoot;
        while (node != null) {
            scx -= node.getCX();
            scy -= node.getCY();
            node = node.getParent();
        }

        double px = scx * scaleFactor + cx;
        double py = scy * scaleFactor + cy;

        Ellipse2D.Double ellipse = new Ellipse2D.Double(px - r, py - r, r * 2, r * 2);
        g.draw(ellipse);
    }

    public void drawSubtreeBounds(Graphics2D g, CirclemapNode selectedNode, Color color) {
    }

    public void drawDescendantSubtreeBounds(Graphics2D g, CirclemapNode parent, Color color) {
    }

    /**
     * Returns the node at the specified view coordinates.
     */
    public CirclemapNode getNodeAt(int px, int py) {
        return getNodeAt((px - cx) / scaleFactor, (py - cy) / scaleFactor);
    }

    /**
     * Returns the node at the specified draw coordinates.
     */
    public CirclemapNode getNodeAt(double px, double py) {
        CirclemapNode parent = drawRoot;
        int depth = 1;
        while (parent != null) {
            px += parent.getCX();
            py += parent.getCY();
            parent = parent.getParent();
            depth--;
        }

        if (root.contains(px, py)) {
            CirclemapNode found = root;
            parent = found;
            do {
                parent = found;
                px -= parent.cx;
                py -= parent.cy;
                for (CirclemapNode node : parent.children()) {
                    if (node.contains(px, py)) {
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

    public void setMaxDepth(int newValue) {
        maxDepth = newValue;
    }

    public int getMaxDepth() {
        return maxDepth;
    }
}
