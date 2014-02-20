/*
 * @(#)HSBColorizer.java  1.0  September 25, 2007
 *
 * Copyright (c) 2007 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

package ch.randelshofer.tree.demo;

import ch.randelshofer.tree.Colorizer;
import java.awt.Color;
import java.util.Arrays;

/**
 * HSBColorizer.
 * 
 * 
 * 
 * @author Werner Randelshofer
 * @version 1.0 September 25, 2007 Created.
 */
public class HSBColorizer implements Colorizer {
    private float[] start;
    private float[] end;
    
    /** Creates a new instance. */
    public HSBColorizer() {
/*        this(new Color(Color.HSBtoRGB(0.66f,0.4f,0.7f)), 
                new Color(Color.HSBtoRGB(0f,0.4f,0.7f)));*/
/*        this(new Color(Color.HSBtoRGB(0f,0.5f,0.8f)), 
                new Color(Color.HSBtoRGB(0.99f,0.5f,0.8f)));*/
        this(Color.white, 
                new Color(0xff9946));
    }
    
    public HSBColorizer(Color start, Color end) {
        this.start = Color.RGBtoHSB(
                start.getRed(), start.getGreen(), start.getBlue(), new float[3]);
        this.end = Color.RGBtoHSB(
                end.getRed(), end.getGreen(), end.getBlue(), new float[3]);
//System.out.println("HSBColorizer start="+Arrays.asList(start)+"  end="+Arrays.asList(end));
    }
    public HSBColorizer(float[] start, float[] end) {
        this.start = start;
        this.end = end;
//System.out.println("HSBColorizer start="+Arrays.asList(start)+"  end="+Arrays.asList(end));
    }
    
    public Color get(float value) {
        return new Color(
                Color.HSBtoRGB(
                start[0] * value + (1f - value) * end[0],
                start[1] * value + (1f - value) * end[1],
                start[2] * value + (1f - value) * end[2]
                )
                );
    }
    
}
