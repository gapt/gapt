/**
 * @(#)MultilineRectmapDraw.java  1.2.1  2012-08-27
 *
 * Copyright (c) 2008-2009 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */package ch.randelshofer.tree.rectmap;

import java.awt.Color;
import java.awt.Shape;
import java.awt.Insets;
import java.awt.Font;
import java.text.AttributedString;
import java.awt.font.TextAttribute;
import java.text.AttributedCharacterIterator;
import java.awt.font.LineBreakMeasurer;
import java.util.LinkedList;
import ch.randelshofer.tree.NodeInfo;
import java.awt.Graphics2D;
import java.awt.font.TextLayout;
import java.awt.geom.Rectangle2D;
import java.util.Iterator;
import javax.swing.SwingConstants;
import static javax.swing.SwingConstants.*;

/**
 * {@code MultilineRectmapDraw}.
 *
 * @author Werner Randelshofer
 * @version 1.2.1 2012-08-27 Fixes memory leak.
 * <br>1.0 2011-08-19 Created.
 */
public class MultilineRectmapDraw extends RectmapDraw {

    private final static int TEXT_ALIGNMENT = SwingConstants.LEFT;
    private final static Insets INSETS = new Insets(4, 4, 4, 4);
    private final static int TAB_SIZE = 8;

    public MultilineRectmapDraw(RectmapNode root, NodeInfo info) {
        super(root, info);
    }

    public MultilineRectmapDraw(RectmapTree model) {
        super(model);
    }

    @Override
    public void drawLabel(Graphics2D g, RectmapNode node, int depth, double px, double py, double sfh, double sfv) {
        //super.drawLabel(g, node, depth, px, py, sfh, sfv);
        if ((node.children().size() == 0 || depth == maxDepth) && node.height *sfv> g.getFont().getSize()) {
            Rectangle2D.Double rect = new Rectangle2D.Double(
                    (px) * sfh + cx, (py) * sfv + cy,
                    node.width * sfh, node.height * sfv);
            String name = info.getName(node.getDataNodePath());
            g.setColor(Color.BLACK);
            drawText(g, name, rect);
        }
    }

    protected void drawText(Graphics2D g, String text, Rectangle2D.Double bounds) {
        if (text != null) {
            Font font = g.getFont();
            boolean isUnderlined = false;
            Insets insets = INSETS;
            Rectangle2D.Double textRect = new Rectangle2D.Double(
                    bounds.x + insets.left,
                    bounds.y + insets.top,
                    bounds.width - insets.left - insets.right,
                    bounds.height - insets.top - insets.bottom);
            float leftMargin = (float) textRect.x;
            float rightMargin = (float) Math.max(leftMargin + 1, textRect.x + textRect.width + 1);
            float verticalPos = (float) textRect.y;
            float maxVerticalPos = (float) (textRect.y + textRect.height);
            if (leftMargin < rightMargin) {
                float tabWidth = (float) (TAB_SIZE * font.getStringBounds("m", g.getFontRenderContext()).getWidth());
                float[] tabStops = new float[(int) (textRect.width / tabWidth)];
                for (int i = 0; i < tabStops.length; i++) {
                    tabStops[i] = (float) (textRect.x + (int) (tabWidth * (i + 1)));
                }

                if (text != null) {
                    Shape savedClipArea = g.getClip();
                    g.clip(textRect);

                    String[] paragraphs = text.split("\n");//Strings.split(getText(), '\n');

                    for (int i = 0; i < paragraphs.length; i++) {
                        if (paragraphs[i].length() == 0) {
                            paragraphs[i] = " ";
                        }
                        AttributedString as = new AttributedString(paragraphs[i]);
                        as.addAttribute(TextAttribute.FONT, font);
                        if (isUnderlined) {
                            as.addAttribute(TextAttribute.UNDERLINE, TextAttribute.UNDERLINE_LOW_ONE_PIXEL);
                        }
                        int tabCount = paragraphs[i].split("\t").length - 1;
                        Rectangle2D.Double paragraphBounds = drawParagraph(g, as.getIterator(), verticalPos, maxVerticalPos, leftMargin, rightMargin, tabStops, tabCount);
                        verticalPos = (float) (paragraphBounds.y + paragraphBounds.height);
                        if (verticalPos > maxVerticalPos) {
                            break;
                        }
                    }
                    g.setClip(savedClipArea);
                }
            }
        }
    }

    /**
     * Draws or measures a paragraph of text at the specified y location and
     * the bounds of the paragraph.
     *
     * @param g Graphics object. This parameter is null, if we want to
     *  measure the size of the paragraph.
     * @param styledText the text of the paragraph.
     * @param verticalPos the top bound of the paragraph
     * @param maxVerticalPos the bottom bound of the paragraph
     * @param leftMargin the left bound of the paragraph
     * @param rightMargin the right bound of the paragraph
     * @param tabStops an array with tab stops
     * @param tabCount the number of entries in tabStops which contain actual
     *        values
     * @return Returns the actual bounds of the paragraph.
     */
    private Rectangle2D.Double drawParagraph(Graphics2D g, AttributedCharacterIterator styledText,
            float verticalPos, float maxVerticalPos, float leftMargin, float rightMargin, float[] tabStops, int tabCount) {
        // This method is based on the code sample given
        // in the class comment of java.awt.font.LineBreakMeasurer, 

        // assume styledText is an AttributedCharacterIterator, and the number
        // of tabs in styledText is tabCount

        Rectangle2D.Double paragraphBounds = new Rectangle2D.Double(leftMargin, verticalPos, 0, 0);

        int[] tabLocations = new int[tabCount + 1];

        int i = 0;
        for (char c = styledText.first(); c != styledText.DONE; c = styledText.next()) {
            if (c == '\t') {
                tabLocations[i++] = styledText.getIndex();
            }
        }
        tabLocations[tabCount] = styledText.getEndIndex() - 1;

        // Now tabLocations has an entry for every tab's offset in
        // the text.  For convenience, the last entry is tabLocations
        // is the offset of the last character in the text.

        LineBreakMeasurer measurer = new LineBreakMeasurer(styledText, g.getFontRenderContext());
        int currentTab = 0;

        while (measurer.getPosition() < styledText.getEndIndex()
                && verticalPos <= maxVerticalPos) {

            // Lay out and draw each line.  All segments on a line
            // must be computed before any drawing can occur, since
            // we must know the largest ascent on the line.
            // TextLayouts are computed and stored in a List;
            // their horizontal positions are stored in a parallel
            // List.

            // lineContainsText is true after first segment is drawn
            boolean lineContainsText = false;
            boolean lineComplete = false;
            float maxAscent = 0, maxDescent = 0;
            float horizontalPos = leftMargin;
            LinkedList<TextLayout> layouts = new LinkedList<TextLayout>();
            LinkedList<Float> penPositions = new LinkedList<Float>();

            int first = layouts.size();

            while (!lineComplete && verticalPos <= maxVerticalPos) {
                float wrappingWidth = rightMargin - horizontalPos;
                TextLayout layout = null;
                layout =
                        measurer.nextLayout(wrappingWidth,
                        tabLocations[currentTab] + 1,
                        lineContainsText);

                // layout can be null if lineContainsText is true
                if (layout != null) {
                    layouts.add(layout);
                    penPositions.add(horizontalPos);
                    horizontalPos += layout.getAdvance();
                    maxAscent = Math.max(maxAscent, layout.getAscent());
                    maxDescent = Math.max(maxDescent,
                            layout.getDescent() + layout.getLeading());
                } else {
                    lineComplete = true;
                }

                lineContainsText = true;

                if (measurer.getPosition() == tabLocations[currentTab] + 1) {
                    currentTab++;
                }

                if (measurer.getPosition() == styledText.getEndIndex()) {
                    lineComplete = true;
                } else if (tabStops.length == 0 || horizontalPos >= tabStops[tabStops.length - 1]) {
                    lineComplete = true;
                }
                if (!lineComplete) {
                    // move to next tab stop
                    int j;
                    for (j = 0; horizontalPos >= tabStops[j]; j++) {
                    }
                    horizontalPos = tabStops[j];
                }
            }
            // If there is only one layout element on the line, and we are
            // drawing, then honor alignemnt
            if (first == layouts.size() - 1 && g != null) {
                switch (TEXT_ALIGNMENT) {
                    case TRAILING:
                        penPositions.set(first, rightMargin - layouts.get(first).getVisibleAdvance() - 1);
                        break;
                    case CENTER:
                        penPositions.set(first, (rightMargin - 1 - leftMargin - layouts.get(first).getVisibleAdvance()) / 2 + leftMargin);
                        break;
                    case LEADING:
                    default:
                        break;
                }
            }



            verticalPos += maxAscent;

            Iterator<TextLayout> layoutEnum = layouts.iterator();
            Iterator<Float> positionEnum = penPositions.iterator();

            // now iterate through layouts and draw them
            while (layoutEnum.hasNext()) {
                TextLayout nextLayout = layoutEnum.next();
                float nextPosition = positionEnum.next();
                if (g != null) {
                    nextLayout.draw(g, nextPosition, verticalPos);
                }
                Rectangle2D layoutBounds = nextLayout.getBounds();
                paragraphBounds.add(new Rectangle2D.Double(layoutBounds.getX() + nextPosition,
                        layoutBounds.getY() + verticalPos,
                        layoutBounds.getWidth(),
                        layoutBounds.getHeight()));
            }

            verticalPos += maxDescent;
        }

        return paragraphBounds;
    }
}
