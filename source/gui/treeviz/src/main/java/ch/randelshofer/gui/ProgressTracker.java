/*
 * @(#)ProgressTracker.java  2.0  2009-03-23
 *
 * Copyright (c) 2008-2009 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */

package ch.randelshofer.gui;

import javax.swing.BoundedRangeModel;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

/**
 * ProgressTracker implements ProgressObserver without providing visual
 * components for the user.
 * 
 * @author Werner Randelshofer
 * @version 2.0 2009-03-23 Updated to new ProgressObserver interface.
 * <br>1.0 2008-07-05 Created.
 */
public class ProgressTracker implements ProgressObserver {
    private String message, note, warning, error;
    private boolean isCanceled,  isClosed,  isCancelable = true, isIndeterminate, isCompleted;
    private javax.swing.BoundedRangeModel model;
    private Runnable doCancel;
    private ChangeListener changeHandler = new ChangeListener() {

        public void stateChanged(ChangeEvent e) {
            if (model != null && model.getValue() >= model.getMaximum()) {
                close();
            }
        }
    };

    /**
     * Creates new form ProgressTracker
     */
    public ProgressTracker(String message, String note, int min, int max) {
        setModel(new javax.swing.DefaultBoundedRangeModel(min, 0, min, max));
       this.message = message;
       this.note = note;
    }

    /**
     * Creates new form ProgressTracker
     */
    public ProgressTracker(String message, String note) {
        setModel(new javax.swing.DefaultBoundedRangeModel(0, 0, 0, 1));
       this.message = message;
       this.note = note;
       this.isIndeterminate = true;
    }

    public void setIndeterminate(boolean newValue) {
        this.isIndeterminate = newValue;

    }

    public void setModel(BoundedRangeModel brm) {
        if (model != null) {
            model.removeChangeListener(changeHandler);
        }
        model = brm;
        if (model != null) {
            model.addChangeListener(changeHandler);
        }
    }

    public BoundedRangeModel getModel() {
        return model;
    }

    /**
     * Set cancelable to false if the operation can not be canceled.
     */
    public void setCancelable(final boolean b) {
        isCancelable = b;
    }

    /**
     * The specified Runnable is executed when the user presses
     * the cancel button.
     */
    public void setDoCancel(Runnable doCancel) {
        this.doCancel = doCancel;
    }

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
    public void setProgress(int nv) {
        model.setValue(nv);
    }

    /**
     * Returns the progress of the operation being monitored.
     */
    public int getProgress() {
        return model.getValue();
    }

    /**
     * Indicate that the operation is complete.  This happens automatically
     * when the value set by setProgress is >= max, but it may be called
     * earlier if the operation ends early.
     */
    public void close() {
        if (!isClosed) {
            isClosed = true;
            if (model != null) {
                model.removeChangeListener(changeHandler);
            }
        }
    }

    /**
     * Returns the minimum value -- the lower end of the progress value.
     *
     * @return an int representing the minimum value
     * @see #setMinimum
     */
    public int getMinimum() {
        return model.getMinimum();
    }

    /**
     * Specifies the minimum value.
     *
     * @param m  an int specifying the minimum value
     * @see #getMinimum
     */
    public void setMinimum(int m) {
        model.setMinimum(m);
    }

    /**
     * Returns the maximum value -- the higher end of the progress value.
     *
     * @return an int representing the maximum value
     * @see #setMaximum
     */
    public int getMaximum() {
        return model.getMaximum();
    }

    /**
     * Specifies the maximum value.
     *
     * @param m  an int specifying the maximum value
     * @see #getMaximum
     */
    public void setMaximum(int m) {
        model.setMaximum(m);
    }

    /**
     * Returns true if the user has hit the Cancel button in the progress dialog.
     */
    public boolean isCanceled() {
        return isCanceled;
    }

    /**
     * Returns true if the ProgressTracker is closed.
     */
    public boolean isClosed() {
        return isClosed;
    }

    /**
     * Cancels the operation.
     * This method must be invoked from the user event dispatch thread.
     */
    public void cancel() {
        if (isCancelable) {
            isCanceled = true;
            note = "Canceling...";
            if (doCancel != null) {
                doCancel.run();
            }
        } else {
                       note = "This process can not be canceled!";
        }
    }

    /**
     * Specifies the additional note that is displayed along with the
     * progress message. Used, for example, to show which file the
     * is currently being copied during a multiple-file copy.
     *
     * @param note  a String specifying the note to display
     * @see #getNote
     */
    public void setNote(String note) {
        if (!isCanceled) {
            this.note = note;
        }
    }

    /**
     * Specifies the additional note that is displayed along with the
     * progress message.
     *
     * @return a String specifying the note to display
     * @see #setNote
     */
    public String getNote() {
        return note;
    }

    public boolean isIndeterminate() {
        return isIndeterminate;
    }

    public void complete() {
        isCompleted = true;
    }

    public boolean isCompleted() {
       return isCompleted;
    }

    public void setWarning(String message) {
        warning = message;
    }

    public String getWarning() {
        return warning;
    }

    public void setError(String message) {
        error = message;
    }

    public String getError() {
        return error;
    }

}
