/*
 * @(#)AbstractNodeInfo.java  1.1  2012-11-28
 * 
 * Copyright (c) 2009-2012 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.demo;

import ch.randelshofer.tree.NodeInfo;
import java.util.*;
import java.util.regex.*;

/**
 * AbstractNodeInfo.
 *
 * @author Werner Randelshofer, Staldenmattweg 2, CH-6410 Goldau
 * @version 1.1 2012-11-28 Adds COLOR_STRING data type. 
 * <br>1.0 2009-02-07 Created.
 */
public abstract class AbstractNodeInfo implements NodeInfo {

    public static enum DataType {

        TEXT_STRING, BOOLEAN_STRING, NUMERIC_STRING, DATE_STRING, LONG, INTEGER,
        COLOR_STRING
    }

    /**
     * Determines the data type of the provided set of data values.
     *
     * @param values String-encoded data values.
     * @return The data type.
     */
    public DataType determineDataType(Set<String> values) {
        Iterator<String> iter = values.iterator();
        if (!iter.hasNext()) {
            return DataType.TEXT_STRING;
        }
        Matcher booleanMatcher = Pattern.compile("true|false").matcher("");
        Matcher numberMatcher = Pattern.compile("^-?\\d+$").matcher("");
        Matcher dateMatcher = Pattern.compile(//
                "^\\d{4}-\\d{2}-\\d{2}(T|\\s)\\d{2}:\\d{2}:\\d{2}$|" +//ISO Date YYYY-DD-MM HH:MM:SS with an optional "T" in front of the time
                "^\\d{2}/\\d{2}/\\d{4}$"//American MM\DD\YYYY
                ).matcher("");
        Matcher colorMatcher = Pattern.compile("#[0-9A-Fa-f]{6}").matcher("");


        // Determine the type of the first value
        String v = iter.next();
        DataType type;
        booleanMatcher.reset(v);
        if (booleanMatcher.matches()) {
            type = DataType.BOOLEAN_STRING;
        } else {
            numberMatcher.reset(v);
            if (numberMatcher.matches()) {
                type = DataType.NUMERIC_STRING;
            } else {
                dateMatcher.reset(v);
                if (dateMatcher.matches()) {
                    type = DataType.DATE_STRING;
                } else {
                    colorMatcher.reset(v);
                    if (colorMatcher.matches()) {
                        type = DataType.COLOR_STRING;
                    } else {
                        type = DataType.TEXT_STRING;
                    }
                }
            }
        }

        // Check all subsequent values against the type of the first
        // value
        if (type != DataType.TEXT_STRING) {
            TypeLoop:
            while (iter.hasNext()) {
                v = iter.next();
                switch (type) {
                    case TEXT_STRING:
                        break TypeLoop;
                    case BOOLEAN_STRING:
                        booleanMatcher.reset(v);
                        if (!booleanMatcher.matches()) {
                            type = DataType.TEXT_STRING;
                            break TypeLoop;
                        }
                        break;
                    case NUMERIC_STRING:
                        numberMatcher.reset(v);
                        if (!numberMatcher.matches()) {
                            type = DataType.TEXT_STRING;
                            break TypeLoop;
                        }
                        break;
                    case DATE_STRING:
                        dateMatcher.reset(v);
                        if (!dateMatcher.matches()) {
                            type = DataType.TEXT_STRING;
                            break TypeLoop;
                        }
                        break;
                    case COLOR_STRING:
                        colorMatcher.reset(v);
                        if (!colorMatcher.matches()) {
                            type = DataType.TEXT_STRING;
                            break TypeLoop;
                        }
                        break;
                }
            }
        }
        return type;
    }
}
