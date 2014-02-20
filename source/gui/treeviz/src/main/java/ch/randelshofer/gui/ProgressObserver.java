/*
 * @(#)ProgressObserver.java  1.1  2007-11-19
 *
 * Copyright (c) 2006 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.. 
 */

package ch.randelshofer.gui;

import javax.swing.*;

/**
 * ProgressObserver.
 * 
 * 
 * @author Werner Randelshofer
 * @version 1.1 2007-11-19 Added method setWarning and setError.
 * <br>1.0 September 18, 2006 Created.
 */
public interface ProgressObserver {
    
    public void setModel(BoundedRangeModel brm);
    
    public BoundedRangeModel getModel();
    
    /**
     * Set cancelable to false if the operation can not be canceled.
     */
    public void setCancelable(boolean b);
    
    /**
     * The specified Runnable is executed when the user presses
     * the cancel button.
     */
    public void setDoCancel(Runnable doCancel);
    
    /**
     * Indicate the progress of the operation being monitored.
     * If the specified value is >= the maximum, the progress
     * monitor is closed.
     * @param nv an int specifying the current value, between the
     *        maximum and minimum specified for this component
     * @see #setMinimum
     * @see #setMaximum
     * @see #close
     */
    public void setProgress(int nv);
    
    /**
     * Returns the progress of the operation being monitored.
     */
    public int getProgress();
    
    /**
     * Returns the minimum value -- the lower end of the progress value.
     *
     * @return an int representing the minimum value
     * @see #setMinimum
     */
    public int getMinimum();
    
    
    /**
     * Specifies the minimum value.
     *
     * @param m  an int specifying the minimum value
     * @see #getMinimum
     */
    public void setMinimum(int m);
    
    
    /**
     * Returns the maximum value -- the higher end of the progress value.
     *
     * @return an int representing the maximum value
     * @see #setMaximum
     */
    public int getMaximum();
    
    
    /**
     * Specifies the maximum value.
     *
     * @param m  an int specifying the maximum value
     * @see #getMaximum
     */
    public void setMaximum(int m);
    
    /**
     * Sets the progress observer to indeterminate.
     */
    public void setIndeterminate(boolean newValue);

    /**
     * Returns true if the progress observer is set to indeterminate.
     */
    public boolean isIndeterminate();
    
    /**
     * Indicate that the operation is complete.  This happens automatically
     * when the value set by setProgress is >= max, but it may be called
     * earlier if the operation ends early.
     */
    public void complete();
    /**
     * Returns true if the operation is completed.
     */
    public boolean isCompleted();
    
    
    /**
     * Cancels the operation.
     * This method must be invoked from the user event dispatch thread.
     */
    public void cancel();
    /**
     * Returns true if the user has hit the Cancel button in the progress dialog.
     */
    public boolean isCanceled();
    
    /**
     * Closes the progress observer.
     */
    public void close();
    /**
     * Returns true if the progress observer is closed.
     */
    public boolean isClosed();
    
    
    /**
     * Specifies the additional note that is displayed along with the
     * progress message. Used, for example, to show which file 
     * is currently being copied during a multiple-file copy.
     *
     * @param note  a String specifying the note to display
     * @see #getNote
     */
    public void setNote(String note);
    
    /**
     * Specifies the additional note that is displayed along with the
     * progress message.
     *
     * @return a String specifying the note to display
     * @see #setNote
     */
    public String getNote();
    
    /**
     * Specifies the additional warning message that is displayed along with the
     * progress message. Used, for example, to show which files couldn't
     * be copied during a multiple-file copy..
     *
     * @param message  a String specifying the message to display, or null
     * if there is no warning.
     * @see #getWarning
     */
    public void setWarning(String message);
    
    /**
     * Specifies the warning message that is displayed along with the
     * progress message.
     *
     * @return a String specifying the message to display, or null if
     * there is no warning.
     */
    public String getWarning();
    
    /**
     * Specifies the additional error message that is displayed along with the
     * progress message. Used, for example, to show which files couldn't
     * be copied during a multiple-file copy..
     *
     * @param message  a String specifying the message to display, or null
     * if there is no error.
     * @see #getWarning
     */
    public void setError(String message);
    
    /**
     * Specifies the error message that is displayed along with the
     * progress message.
     *
     * @return a String specifying the message to display, or null if
     * there is no error.
     */
    public String getError();
}
