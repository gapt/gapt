/**
 * @(#)ColorStringColorizer.java  2012-11-28
 *
 * Copyright (c) 2012 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.demo;

import ch.randelshofer.tree.Colorizer;
import java.awt.Color;

/**
 * ColorStringColorizer displays the color given by the color string data value.
 *
 * @author Werner Randelshofer
 * @version 1.0 2012-11-28 Created.
 */
public class ColorStringColorizer implements Colorizer {

    public ColorStringColorizer() {
    }

    @Override
    public Color get(float value) {
        return new Color(Float.floatToIntBits(value));
    }
}
