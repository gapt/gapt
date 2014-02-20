/*
 * @(#)Complex.java  1.0  2008-07-07
 *
 * Copyright (c) 2008 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.util;

/**
 * Immutable complex number of the form x+bi.
 *
 * @author Werner Randelshofer
 * @version 1.0 2008-07-07 Created.
 */
public class Complex implements Cloneable {

    private double x;
    private double y;

    /**
     * Creates a complex number with the real part x and the
     * imaginary part y.
     * 
     * @param x real part of the complex number
     * @param y imaginary part of the complex number
     */
    public Complex(double x, double y) {
        this.x = x;
        this.y = y;
    }

    /**
     * Returns the real part of the complex number.
     * @return real part.
     */
    public double real() {
        return x;
    }

    /**
     * Returns the imaginary part of the complex number.
     * @return real part.
     */
    public double img() {
        return y;
    }

    /**
     * Returns a complex number whose value is (this + that).
     * 
     * @param that A complex number.
     * @return this + that.
     */
    public Complex add(Complex that) {
        return new Complex(this.x + that.x, this.y + that.y);
    }

    /**
     * Returns a complex number whose value is (a + b).
     * 
     * @param a A complex number.
     * @param b A complex number.
     * @return a + b.
     */
    public static Complex add(Complex a, Complex b) {
        return a.add(b);
    }

    /**
     * Returns a complex number whose value is (this - that).
     * 
     * @param that A complex number.
     * @return this - that.
     */
    public Complex sub(Complex that) {
        return new Complex(this.x - that.x, this.y - that.y);
    }

    /**
     * Returns a complex number whose value is (a - b).
     * 
     * @param a A complex number.
     * @param b A complex number.
     * @return a - b.
     */
    public static Complex sub(Complex a, Complex b) {
        return a.sub(b);
    }

    /**
     * Returns a complex number whose value is (this * that).
     * 
     * @param that A complex number.
     * @return this * that.
     */
    public Complex mul(Complex that) {
        return new Complex(this.x * that.x - this.y * that.y, this.x * that.y + this.y * that.x);
    }

    /**
     * Returns a complex number whose value is (a * b).
     * 
     * @param a A complex number.
     * @param b A complex number.
     * @return a * b.
     */
    public static Complex mul(Complex a, Complex b) {
        return a.mul(b);
    }

    /**
     * Returns a complex number whose value is (this / that).
     * 
     * @param that A complex number.
     * @return this / that.
     */
    public Complex div(Complex that) {
        return new Complex((this.x * that.x + this.y * that.y) / (that.x * that.x + that.y * that.y),
                (this.y * that.x - this.x * that.y) / (that.x * that.x + that.y * that.y));
    }

    /**
     * Returns a complex number whose value is (a / b).
     * 
     * @param a A complex number.
     * @param b A complex number.
     * @return a / b.
     */
    public static Complex div(Complex a, Complex b) {
        return a.div(b);
    }

    /**
     * Returns the argument of this complex number 
     * (the angle in radians with the x-axis in polar coordinates).
     * 
     * @return atan2(y, x).
     */
    public double arg() {
        return Math.atan2(y, x);
    }

    /**
     * Returns the modulo of this complex number.
     * 
     * @return sqrt(x*x + y*y).
     */
    public double mod() {
        return Math.sqrt(x * x + y * y);
    }

    /**
     * Returns the principal branch of the square root of this complex number.
     * 
     * @return square root.
     */
    public Complex sqrt() {
        double r = Math.sqrt(mod());
        double theta = this.arg() / 2;
        return new Complex(r * Math.cos(theta), r * Math.sin(theta));
    }

    /**
     * Returns true of this complex number is equal to the specified
     * complex number.
     * 
     * @return true if equal.
     */
    @Override
    public boolean equals(Object o) {
        if (o instanceof Complex) {
            Complex that = (Complex) o;
            return that.x == this.x && that.y == this.y;
        }
        return false;
    }

    /**
     * Returns a hash code for this complex number.
     * 
     * @return hash code.
     */
    @Override
    public int hashCode() {
        long bits = java.lang.Double.doubleToLongBits(x);
        bits ^= java.lang.Double.doubleToLongBits(y) * 31;
        return (((int) bits) ^ ((int) (bits >> 32)));
    }

    /**
     * Returns a clone of this complex number.
     * 
     * @return a clone.
     */
    @Override
    public Complex clone() {
        try {
            return (Complex) super.clone();
        } catch (CloneNotSupportedException ex) {
            throw new InternalError("Cloneable not implemented");
        }
    }

    /**
     * Returns a descriptive string representation of this complex number.
     * 
     * @return a descriptive string.
     */
    @Override
    public String toString() {
        if (y >= 0) {
            return "(" + x + "+" + y + "i)";
        } else {
            return "(" + x + "" + y + "i)";
        }
    }

    /**
     * Returns true if this complex numer is not a number (NaN).
     * 
     * @return true if NaN.
     */
    public boolean isNaN() {
        return Double.isNaN(x) || Double.isNaN(y);
    }

    public static void main(String[] args) {
        // Addition: (3+2i)+(5+5i) = (8+7i):
        System.out.println(new Complex(3, 2).add(new Complex(5, 5)));

        // Subtraction: (5+5i)-(3+2i) = (2-3i):
        System.out.println(new Complex(5, 5).sub(new Complex(3, 2)));

        // Multiplication: (2+5i)*(3+7i) = (-29+29i):
        System.out.println(new Complex(2, 5).mul(new Complex(3, 7)));

        // Division: (2+5i)/(3+7i) = (0.706896+0.017241i):
        System.out.println(new Complex(2, 5).div(new Complex(3, 7)));

        // Square Root: (4+0i) = (2+0i)
        System.out.println(new Complex(4, 0).sqrt());

        // Square Root: (2+0i)+(2+0i) = (2+0i)
        System.out.println(new Complex(2, 0).add(new Complex(2, 0)).sqrt());

        // Square Root: (1+0i) = (1+0i)
        System.out.println(new Complex(1, 0).sqrt());
        // Square Root: (3+4i) = (2+0i)
        System.out.println(new Complex(3, 4).sqrt());
        // Square Root: (-9+0i) = (0+3i)
        System.out.println(new Complex(-9, 0).sqrt());
    }
}
