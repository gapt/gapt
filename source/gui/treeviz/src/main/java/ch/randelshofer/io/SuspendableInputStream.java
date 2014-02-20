/*
 * @(#)SuspendableInputStream.java  1.0.1  2003-04-25
 *
 * Copyright (c) 1999-2003 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.io;

import java.io.FilterInputStream;
import java.io.InputStream;
import java.io.IOException;


/**
 * This input stream can be used to suspend, resume and abort a worker thread
 * who is reading an input stream.
 * The methods #suspend, #resume and #abort must by called from a different
 * thread (the supervising thread).
 *
 * @author Werner Randelshofer, Staldenmattweg 2, CH-6410 Goldau, Switzerland
 * @version 1.0.1 2003-04-25 Source code complies now to Java Code Conventions.
 * <br>1.0 1999-05-09  Created.
 */
public class SuspendableInputStream
extends FilterInputStream {
    private final static int ACTIVE = 0;
    private final static int SUSPENDED = 1;
    private final static int ABORTED = 2;
    
    private volatile int state = ACTIVE;
    
    public SuspendableInputStream(InputStream in) {
        super(in);
    }
    
    public synchronized void suspend() {
        if (state == ACTIVE) {
            state = SUSPENDED;
            notifyAll();
        }
    }
    
    public synchronized void resume() {
        if (state == SUSPENDED) {
            state = ACTIVE;
            notifyAll();
        }
    }
    
    public synchronized void abort() {
        if (state != ABORTED) {
            state = ABORTED;
            notifyAll();
        }
    }
    
    public boolean isSuspended() {
        return state == SUSPENDED; 
    }
    
    public boolean isAborted() {
        return state == ABORTED; 
    }
    
    public int read()
    throws IOException {
        synchronized(this) {
            while (state == SUSPENDED) {
                try { wait(); }
                catch (InterruptedException e) {}
            }
        }
        if (state == ABORTED) {
            throw new IOException("Aborted");
        }
        return super.read();
    }
    public int read(byte[] b)
    throws IOException {
        synchronized(this) {
            while (state == SUSPENDED) {
                try { wait(); }
                catch (InterruptedException e) {}
            }
        }
        if (state == ABORTED) { 
            throw new IOException("Aborted");
        }
        return super.read(b);
    }
    public int read(byte[] b, int off, int len)
    throws IOException {
        synchronized(this) {
            while (state == SUSPENDED) {
                try { wait(); }
                catch (InterruptedException e) {}
            }
        }
        if (state == ABORTED) { 
            throw new IOException("Aborted"); 
        }
        return super.read(b,off,len);
    }
}
