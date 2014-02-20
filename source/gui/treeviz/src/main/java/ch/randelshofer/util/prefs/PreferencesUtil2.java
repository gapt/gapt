/*
 * @(#)PreferencesUtil2.java  1.0  2011-01-20
 * 
 * Copyright (c) 2011 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 * 
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.util.prefs;

import java.io.IOException;
import java.io.OutputStream;
import java.security.AccessControlException;
import java.util.HashMap;
import java.util.prefs.BackingStoreException;
import java.util.prefs.NodeChangeListener;
import java.util.prefs.PreferenceChangeListener;
import java.util.prefs.Preferences;

/**
 * {@code PreferencesUtil2}.
 *
 * @author Werner Randelshofer
 * @version 1.0 2011-01-20 Created.
 */
public class PreferencesUtil2 extends Preferences {

    private static HashMap<Package,PreferencesUtil2> userNodes;
    private static HashMap<Package,PreferencesUtil2> systemNodes;

    private HashMap<String, String> data = new HashMap<String, String>();
    private final boolean isUserNode;

    private PreferencesUtil2(boolean isUserNode) {
        this.isUserNode=isUserNode;
    }

    @Override
    public synchronized void put(String key, String value) {
        data.put(key, value);
    }

    @Override
    public synchronized String get(String key, String def) {
        return data.containsKey(key) ? data.get(key) : def;
    }

    @Override
    public synchronized void remove(String key) {
        data.remove(key);
    }

    @Override
    public synchronized void clear() {
        data.clear();
    }

    @Override
    public synchronized void putInt(String key, int value) {
        data.put(key, Integer.toString(value));
    }

    @Override
    public synchronized int getInt(String key, int def) {
        return data.containsKey(key) ? Integer.parseInt(data.get(key)) : def;

    }

    @Override
    public synchronized void putLong(String key, long value) {
        data.put(key, Long.toString(value));
    }

    @Override
    public synchronized long getLong(String key, long def) {
        return data.containsKey(key) ? Long.parseLong(data.get(key)) : def;
    }

    @Override
    public synchronized void putBoolean(String key, boolean value) {
        data.put(key, Boolean.toString(value));
    }

    @Override
    public synchronized boolean getBoolean(String key, boolean def) {
        return data.containsKey(key) ? Boolean.parseBoolean(data.get(key)) : def;
    }

    @Override
    public synchronized void putFloat(String key, float value) {
        data.put(key, Float.toString(value));
    }

    @Override
    public synchronized float getFloat(String key, float def) {
        return data.containsKey(key) ? Float.parseFloat(data.get(key)) : def;
    }

    @Override
    public synchronized void putDouble(String key, double value) {
        data.put(key, Double.toString(value));
    }

    @Override
    public synchronized double getDouble(String key, double def) {
        return data.containsKey(key) ? Double.parseDouble(data.get(key)) : def;
    }

    @Override
    public synchronized void putByteArray(String key, byte[] value) {
        StringBuilder buf = new StringBuilder();
        for (int i = 0; i < value.length; ++i) {
            if (i != 0) {
                buf.append(',');
            }
            buf.append(Byte.toString(value[i]));
        }
        data.put(key, buf.toString());
    }

    @Override
    public synchronized byte[] getByteArray(String key, byte[] def) {
        if (data.containsKey(key)) {
            String[] strs = data.get(key).split(",");
            byte[] value = new byte[strs.length];
            for (int i = 0; i < value.length; ++i) {
                value[i] = Byte.parseByte(strs[i]);
            }
            return value;
        } else {
            return def;
        }
    }

    @Override
    public synchronized String[] keys()  {
        return data.keySet().toArray(new String[data.size()]);
    }

    @Override
    public synchronized String[] childrenNames() throws BackingStoreException {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public synchronized Preferences parent() {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public synchronized Preferences node(String pathName) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public synchronized boolean nodeExists(String pathName) throws BackingStoreException {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public synchronized void removeNode() throws BackingStoreException {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public synchronized String name() {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public synchronized String absolutePath() {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public synchronized boolean isUserNode() {
        return isUserNode();
    }

    @Override
    public synchronized String toString() {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public synchronized void flush() throws BackingStoreException {
       //do nothing
    }

    @Override
    public synchronized void sync() throws BackingStoreException {
       //do nothing
    }

    @Override
    public synchronized void addPreferenceChangeListener(PreferenceChangeListener pcl) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public synchronized void removePreferenceChangeListener(PreferenceChangeListener pcl) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public synchronized void addNodeChangeListener(NodeChangeListener ncl) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public synchronized void removeNodeChangeListener(NodeChangeListener ncl) {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public synchronized void exportNode(OutputStream os) throws IOException, BackingStoreException {
        throw new UnsupportedOperationException("Not supported yet.");
    }

    @Override
    public synchronized void exportSubtree(OutputStream os) throws IOException, BackingStoreException {
        throw new UnsupportedOperationException("Not supported yet.");
    }
    public synchronized static Preferences systemNodeForPackage(Class<?> c) {
        try {
        return Preferences.systemNodeForPackage(c);
        } catch (AccessControlException e) {
            if (systemNodes==null) {
                systemNodes=new HashMap<Package,PreferencesUtil2>();
            }
            if (!systemNodes.containsKey(c.getPackage())) {
                systemNodes.put(c.getPackage(),new PreferencesUtil2(false));
            }
            return systemNodes.get(c.getPackage());
        }
    }
   public synchronized static Preferences userNodeForPackage(Class<?> c) {
        try {
        return Preferences.userNodeForPackage(c);
        } catch (AccessControlException e) {
            if (userNodes==null) {
                userNodes=new HashMap<Package,PreferencesUtil2>();
            }
            if (!userNodes.containsKey(c.getPackage())) {
                userNodes.put(c.getPackage(),new PreferencesUtil2(true));
            }
            return userNodes.get(c.getPackage());
        }
    }
}
