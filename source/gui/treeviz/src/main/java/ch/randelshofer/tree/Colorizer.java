/*
 * @(#)Colorizer.java  1.0  September 25, 2007
 *
 * Copyright (c) 2007 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

package ch.randelshofer.tree;

import java.awt.Color;

/**
 * Colorizer.
 * 
 * 
 * 
 * 
 * @author Werner Randelshofer
 * @version 1.0 September 25, 2007 Created.
 */
public interface Colorizer {
    
    /**
     * Gets a color for the specified value.
     * @param value A value between 0 and 1.
     */
    public Color get(float value);
    
}
