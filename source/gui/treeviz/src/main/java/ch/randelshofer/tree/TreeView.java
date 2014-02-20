/*
 * @(#)TreeView.java  2.0  2009-01-30
 * 
 * Copyright (c) 2008 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms..
 */

package ch.randelshofer.tree;

import java.awt.event.MouseEvent;

/**
 * TreeView.
 *
 * @author Werner Randelshofer, Staldenmattweg 2, CH-6410 Goldau
 * @version 2.0 2009-01-30 Added maxDepth property.
 * <br>1.0 2008-10-22 Created.
 */
public interface TreeView {

    public void setMaxDepth(int newValue);
    public int getMaxDepth();
    public void setToolTipEnabled(boolean newValue);
    public boolean isToolTipEnabled();
    public String getInfoText(MouseEvent evt);
    public void repaintView();
}
