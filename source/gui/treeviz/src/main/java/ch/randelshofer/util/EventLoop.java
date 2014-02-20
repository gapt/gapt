/*
 * @(#)EventLoop.java  1.3  2002-05-15
 *
 * Copyright (c) 2001 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms. 
 */
package ch.randelshofer.util;

import java.util.*;
/**
 * An EventLoop can process events on a separate worker thread.
 * It consists of two parts: the event collector and the event
 * processor.
 * <p>
 * The event collector collects all incoming events and puts them
 * into a queue.<br>
 * The event processor removes the events from the queue and 
 * processes them.
 * <p>
 * The key feature of the EventLoop is, that clients don't have
 * to wait until an event has been processed. Clients are free
 * to proceed as soon as the collector has put the event into
 * the queue.
 * <p>
 * Other important features are that events are processed in
 * the same sequence as they have been collected and that only one
 * thread is used to process the events.
 * <p>
 * <b>Usage</b>
 * <p>
 * This is an abstract class. It does all the queue handling, but
 * does no processing. To use it, you have to create a subclass
 * which overrides the methods #collectEvent and #processEvent.
 * <p>
 * <b>Example</b>
 * <p>
 * An EventLoop, which outputs Strings on a background thread
 * could look like this:
 * <pre><tt>
 * public class AsyncDisplay
 * extends AbstractEventLoop {
 *     public void display(String string) {
 *         collectEvent(string);
 *     }
 *     protected void processEvent(Object event) {
 *          System.out.println((String) event);
 *    }
 * }
 * </tt></pre>
 * <p>
 * To use the class proceed like this:
 * <p><pre><tt>
 * AsyncDisplay a = new AsyncDisplay();
 *  a.display("Hello World");
 * </tt></pre>
 *
 * @author Werner Randelshofer
 * @version 1.3 2002-05-15 Reworked.
 * <br>1.2 2001-09-24 Support for coalescing of events added.
 * <br>1.1 2001-08-24 Reworked for JDK 1.3.
 * <br>1.0.2   2000-03-03
 *        Catch SecurityException's (To make this class work in Netscape Navigator).
 * <br>history 1.0.1  14.10.1998
 *     Versionskennung in Klassenkommentar eingefügt.
 * <br>history  1.0  Datum ?
 *    Threads werden nicht mehr wiederverwendet.
 */
public abstract class EventLoop {
    /**
     * The event processor thread.
     */
    private Thread eventProcessor;

    /**
     * The priority of the processor thread.
     */
    private int priority;
    
    /**
     * The queue stores the events until they
     * can be processed by a processor thread.
     */
    private final LinkedList queue = new LinkedList();
    
    /**
     * Indicates whether multiple events will be coalesced
     * by the event processor or not.
     */
    private boolean isCoalesce;
    /**
     * Indicates whether events will be processed by the
     * event processor or not.
     */
    private volatile boolean isAlive = true;
    
    /**
     * Creates a new EventLoop which processes events at Thread.NORM_PRORITY.
     */
    public EventLoop() {
        this(Thread.NORM_PRIORITY);
    }
    /**
     * Creates a new EventLoop which processes events at the 
     * desired thread priority.
     *
     * @param priority The Thread priority of the event processor.
     */
    public EventLoop(int priority) {
        this.priority = priority;
    }
    /**
     * Collects an event and puts it into the event queue
     * for later processing.
     * 
     * @param event The event to be put into the queue.
     */
    protected void collectEvent(Object event) {
        synchronized(queue) {
            if (! isCoalesce || ! queue.contains(event)) {
                queue.addLast(event);
                if (isAlive) startProcessor();
            }
        }
    }

    /**
     * Sets whether the EventLoop coalesces multiple pending events. 
     * A busy application may not be able to keep up with event 
     * generation, causing multiple events to be queued. 
     * Coalescing is based on equality tests of event objects.
     * More formally, coalesces an event o if and only if the queue
     * contains at least one element e such that
     * <code>(o==null ? e==null : o.equals(e))</code>.
     * <p>
     * EventLoops do not coalesce events by default.
     *
     * @param b Specify true to turn on coalescing. 
     */
    public void setCoalesce(boolean b) {
        isCoalesce = b;
    }
    /**
     * Returns true if the EventLoop
     * coalesces multiple pending events.
     *
     * @see setCoalesce(boolean)
     */
    public boolean isCoalesce() {
        return isCoalesce;
    }
    
    /**
     * Starts the event processor.
     * <br>The event processor is started by default.
     */
    public void start() {
        synchronized(queue) {
            isAlive = true;
            startProcessor();
        }
    }
    
    /**
     * Stops the event processor.
     */
    public void stop() {
        isAlive = false;
    }

    /**
     * Clears the event queue.
     */
    public void clear() {
        synchronized(queue) {
            queue.clear();
        }
    }

    /**
     * This is the method which really starts the processor.
     */
    private void startProcessor() {
        synchronized(queue) {
            if (eventProcessor == null) {
                eventProcessor = new Thread(this+" Event Processor") {
                    public void run() {
                        processEvents();
                    }
                };
                try { 
                    // The event processor must not be a daemon.
                    // If it was a daemon, the virtual machine would
                    // stop before the event had been processed.
                    eventProcessor.setDaemon(false);
                } catch (SecurityException e) {}
                try {
                    eventProcessor.setPriority(priority);
                } catch (SecurityException e) {}
                eventProcessor.start();
            }
        }
    }
    
    /**
     * This method processes a single event on the event processor thread.
     *
     * @param event An event from the queue.
    */
   protected abstract void processEvent(Object event);

    /**
     * This method removes events from the event queue
     * and proceses them until the queue is empty or
     * until #stop is called.
     * <p>
     * This method must be called from the event processor
     * thread only.
     */
    protected void processEvents() {
        Object event;
        while (isAlive) {
            synchronized(queue) {
                if (queue.isEmpty()) {
                    eventProcessor = null;
                    return;
                }
                event = queue.removeFirst();
            }
            try {
                processEvent(event);
            } catch (Throwable e) {
                e.printStackTrace();
            }
        }
    }
}
