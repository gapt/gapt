/*
 * @(#)Worker.java
 *
 * Copyright (c) 1996-2011  Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.util;

import javax.swing.JOptionPane;
import javax.swing.SwingUtilities;

/**
 * This is an abstract class that you subclass to
 * perform GUI-related work in a dedicated event dispatcher.
 * <p>
 * This class is similar to SwingWorker but less complex.
 *
 * @author Werner Randelshofer
 * @version $Id: Worker.java 557 2009-09-06 16:12:08Z rawcoder $
 */
public abstract class Worker<T> implements Runnable {

    private T value;  // see getValue(), setValue()
    private Throwable error;  // see getError(), setError()

    /**
     * Calls #construct on the current thread and invokes
     * #done on the AWT event dispatcher thread.
     */
    public final void run() {
        try {
            setValue(construct());
        } catch (Throwable e) {
            setError(e);
            SwingUtilities.invokeLater(new Runnable() {

                public void run() {
                    failed(getError());
                    finished();
                }
            });
            return;
        }
        SwingUtilities.invokeLater(new Runnable() {

            public void run() {
                try {
                done(getValue());
                } finally {
                finished();
                }
            }
        });
    }

    /**
     * Compute the value to be returned by the <code>get</code> method.
     */
    protected abstract T construct() throws Exception;

    /**
     * Called on the event dispatching thread (not on the worker thread)
     * after the <code>construct</code> method has returned without throwing
     * an error.
     * <p>
     * The default implementation does nothing. Subclasses may override this
     * method to perform done actions on the Event Dispatch Thread.
     *
     * @param value The return value of the construct method.
     */
    protected void done(T value) {
    }

    /**
     * Called on the event dispatching thread (not on the worker thread)
     * after the <code>construct</code> method has thrown an error.
     * <p>
     * The default implementation prints a stack trace. Subclasses may override
     * this method to perform failure actions on the Event Dispatch Thread.
     *
     * @param error The error thrown by construct.
     */
    protected void failed(Throwable error) {
                JOptionPane.showMessageDialog(null, error.getMessage(),"Error",JOptionPane.ERROR_MESSAGE);
        error.printStackTrace();
    }

    /**
     * Called on the event dispatching thread (not on the worker thread)
     * after the <code>construct</code> method has finished and after
     * done() or failed() has been invoked.
     * <p>
     * The default implementation does nothing. Subclasses may override this
     * method to perform completion actions on the Event Dispatch Thread.
     */
    protected void finished() {
    }

    /**
     * Get the value produced by the worker thread, or null if it
     * hasn't been constructed yet.
     */
    protected synchronized T getValue() {
        return value;
    }

    /**
     * Set the value produced by construct.
     */
    private synchronized void setValue(T x) {
        value = x;
    }

    /**
     * Get the error produced by the worker thread, or null if it
     * hasn't thrown one.
     */
    protected synchronized Throwable getError() {
        return error;
    }

    /**
     * Set the error thrown by constrct.
     */
    private synchronized void setError(Throwable x) {
        error = x;
    }

    /**
     * Starts the Worker on an internal worker thread.
     */
    public void start() {
        new Thread(this).start();
    }
}
