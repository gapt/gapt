/**
 * @(#)CircleRadiusComparator.java  1.0  Jan 17, 2008
 *
 * Copyright (c) 2008 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

package ch.randelshofer.tree.circlemap;

import java.util.Comparator;

/**
 * Compares two circles by the size of their radius.
 *
 * @author Werner Randelshofer
 * @version 1.0 Jan 17, 2008 Created.
 */
public class CircleRadiusComparator implements Comparator<Circle> {
    private static CircleRadiusComparator ascendingInstance;
    private static CircleRadiusComparator descendingInstance;
    private int asc = 1;
    
    public static CircleRadiusComparator getAscendingInstance() {
        if (ascendingInstance == null) {
            ascendingInstance = new CircleRadiusComparator();
        }
        return ascendingInstance;
    }
    public static CircleRadiusComparator getDescendingInstance() {
        if (descendingInstance == null) {
            descendingInstance = new CircleRadiusComparator();
            descendingInstance.asc = -1;
        }
        return descendingInstance;
    }
    

    
    
    public int compare(Circle c1, Circle c2) {
        double cmp = c1.radius - c2.radius;
        return (cmp < 0) ? -asc : ((cmp > 0) ? asc : 0);
    }
}
