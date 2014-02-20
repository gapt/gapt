/*
 * @(#)FileSizeFormat.java  1.1.1  2010-06-20
 *
 * Copyright (c) 2009 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

package ch.randelshofer.text;

import java.text.DecimalFormat;
import java.text.NumberFormat;

/**
 * Formats units in bytes into a human readable string.
 *
 * FIXME - Rework this, so that we can specify the number of desired digits.
 *
 * @author Werner Randelshofer
 * @version 1.1.1 2010-06-20 Don't scale byte values to kilobytes.
 * <br>1.1 2009-07-05 By default use megabyte units instead of mebibyte units.
 * <br>1.0 2009-03-20 Created.
 */
public class FileSizeFormat {
    private static NumberFormat intFormat = DecimalFormat.getIntegerInstance();

    private NumberFormat decimalFormat;
    private static FileSizeFormat instance;
    private boolean isAlwaysIncludeBytes = false;
    private boolean isShort = false;

    /** The highest numeric value with a desired number of digits.
     * For example 999 for 3 digits.
     */
    private int limit = 999;
    /** The scale factor for the next unit.
     * 1000 for megabyte-units. 1024 for mebibyte-units.
     *
     * See: http://en.wikipedia.org/wiki/Megabyte
     */
    private int scale = 1024;

    public FileSizeFormat() {
        decimalFormat = (NumberFormat) DecimalFormat.getNumberInstance().clone();
        decimalFormat.setMaximumFractionDigits(1);
    }


    public void setMaximumFractionDigits(int newValue) {
        decimalFormat.setMaximumFractionDigits(newValue);
    }
    public void setAlwaysIncludeBytes(boolean newValue) {
        isAlwaysIncludeBytes = newValue;
    }
    public void setShortFormat(boolean newValue) {
        isShort = newValue;
    }

    public void setMebibyte(boolean isMebibyte) {
        if (isMebibyte) {
            scale = 1024;
        } else {
            scale = 1000;
        }
    }
    public boolean isMebibyte() {
      return scale == 1024;
    }


    /**
     * Returns a medium version of the formatted string.
     * @param w Units in bytes.
     * @return Formatted string.
     */
    public String format(long w) {

        return (isShort) ? formatShort(w) : formatLong(w);
    }

    /**
     * Returns a long version of the formatted string.
     * @param w Units in bytes.
     * @return Formatted string.
     */
    public String formatLong(long w) {
        double scaledW = w;
        String scaledUnit = "bytes";
        if (scaledW > limit) {
            scaledW /= scale;
            scaledUnit = "KB";
            if (scaledW > limit) {
                scaledW /= scale;
                scaledUnit = "MB";
                if (scaledW > limit) {
                    scaledW /= scale;
                    scaledUnit = "GB";
                    if (scaledW > limit) {
                        scaledW /= scale;
                        scaledUnit = "TB";
                    }
                }
            }
        }
        StringBuilder buf = new StringBuilder();
        buf.append(decimalFormat.format(scaledW));
        buf.append(' ');
        buf.append(scaledUnit);
        if (isAlwaysIncludeBytes && scaledUnit != "bytes") { // string literals get interned
            buf.append(" (");
            buf.append(decimalFormat.format(w));
            buf.append(" bytes)");
        }
        return buf.toString();
    }

    /**
     * Returns a short version of the formatted string.
     * @param w Units in bytes.
     * @return Formatted string.
     */
    public String formatShort(long w) {
        double scaledW = w;
        String scaledUnit = "bytes";
        if (scaledW > limit) {
            scaledW /= scale;
            scaledUnit = "K";
            if (scaledW > limit) {
                scaledW /= scale;
                scaledUnit = "M";
                if (scaledW > limit) {
                    scaledW /= scale;
                    scaledUnit = "G";
                    if (scaledW > limit) {
                        scaledW /= scale;
                        scaledUnit = "T";
                    }
                }
            }
        }
        StringBuilder buf = new StringBuilder();
        if (scaledUnit == "bytes") { // string literals get interned
            buf.append(decimalFormat.format(scaledW));
            buf.append("B");
        } else {
            if (scaledW < 10d) {
                buf.append(decimalFormat.format(scaledW));
            } else {
                buf.append(intFormat.format(scaledW));
            }
            buf.append(scaledUnit);
        }
        return buf.toString();
    }

    public static FileSizeFormat  getInstance() {
        if (instance == null) {
            instance = new FileSizeFormat();
        }
        return instance;

    }
}
