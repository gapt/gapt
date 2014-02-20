/**
 * @(#)Circles.java  1.2  2008-07-05
 *
 * Copyright (rc) 2008 Werner Randelshofer, Goldau, Switzerland.
 * All rights reserved.
 *
 * You may not use, copy or modify this file, except in compliance with the
 * license agreement you entered into with Werner Randelshofer.
 * For details see accompanying license terms.
 */
package ch.randelshofer.tree.circlemap;

import ch.randelshofer.util.Complex;
import java.awt.geom.*;
import java.util.*;
import java.util.*;
import java.util.concurrent.CyclicBarrier;

/**
 * Utility functions for {@link Circle} objects.
 *
 * @author Werner Randelshofer
 * @version 1.2 2008-07-05 Method boundingCircle treats now 3 circles as a 
 * special case. 
 * <br>1.1 2008-06-12 Make pair.innerSoddyRadius smaller every time
 * we fail to insert a circle at it.
 * <br>1.0 Jan 17, 2008 Created.
 */
public class Circles {

    /** Prevent instance creation. */
    private Circles() {
    }

    /**
     * Calculate the bounding box of all circles.
     * @param circles
     * @return the bounding box.
     */
    public static Rectangle2D.Double boundingBox(ArrayList<Circle> circles) {
        double minx = Double.MAX_VALUE, maxx = Double.MIN_VALUE;
        double miny = Double.MAX_VALUE, maxy = Double.MIN_VALUE;

        for (Circle c : circles) {
            minx = Math.min(minx, c.cx - c.radius);
            maxx = Math.max(maxx, c.cx + c.radius);
            miny = Math.min(miny, c.cy - c.radius);
            maxy = Math.max(maxy, c.cy + c.radius);
        }

        return new Rectangle2D.Double(minx, miny, maxx - minx, maxy - miny);
    }

    /**
     * Calculate the bounding circle of all circles.
     * @param circles
     * @return the bounding circle.
     */
    public static Circle boundingCircle(ArrayList<Circle> circles) {
        // The following algorithm calculates a bounding circle
        // which is tangent to at least one of the given circles


        // Bounding soddy circle: Try to find a bounding circle which is tangent
        // to three of the given circles (soddy circle), and contains
        // them all.
        Circle outerSoddy = null;
        if (circles.size() >= 3) {
            outerSoddy = outerSoddyCircle(circles.get(0), circles.get(1), circles.get(2));
            for (Circle c : circles) {
                double dist = Math.sqrt(
                        (outerSoddy.cx - c.cx) * (outerSoddy.cx - c.cx) +
                        (outerSoddy.cy - c.cy) * (outerSoddy.cy - c.cy));
                outerSoddy.radius = Math.max(outerSoddy.radius, dist + c.radius);
            }
        }


        // Bounding tangent circle: Find a bounding circle which is tangent
        // to one of the given circles
        Rectangle2D.Double bbox = boundingBox(circles);
        Circle bc = new Circle(bbox.getCenterX(), bbox.getCenterY(),
                Math.max(bbox.width, bbox.height) / 2);
        for (Circle c : circles) {
            double dist = Math.sqrt(
                    (bc.cx - c.cx) * (bc.cx - c.cx) +
                    (bc.cy - c.cy) * (bc.cy - c.cy));
            bc.radius = Math.max(bc.radius, dist + c.radius);
        }

        // Return the smaller of the bounding tangent circle and the bounding
        // soddy circle (if it exists).
        return (outerSoddy == null || bc.radius < outerSoddy.radius) ? bc : outerSoddy;
    }


    /**
     * Packs circles closely together into a circle around the center of
     * the coordinate system using a phyllotactic pattern.
     * <p>
     * Phyllotactic patterns occur in nature, for example in the seeds of a 
     * sunflower.
     * <p>
     * In a phyllotactic pattern, the polar coordinates for the {@code n}th object
     * are:
     * <pre>
     * radius = rc * Math.sqrt(i+1),
     * ra = (i+1) * 137.5°
     * </pre>
     * Where {@code rc} is the spacing constant, and 137.5° is the angular constant.
     * <p>
     * The current implementation yields only good results, if
     * all circles are of the same size.
     *
     * 
     * @param circles
     */
    public static void phyllotacticPack(ArrayList<Circle> circles) {
        switch (circles.size()) {
            case 0:
                break;
            case 1:
                 {
                    Circle circle = circles.get(0);
                    circle.cx = 0;
                    circle.cy = 0;
                }
                break;
            case 2:
                 {
                    Circle c0 = circles.get(0);
                    Circle c1 = circles.get(1);
                    double radius = c0.radius + c1.radius;
                    c0.cx = c0.radius - radius;
                    c1.cx = radius - c1.radius;
                    c0.cy = c1.cy = 0;
                }
                break;
            case 3:
                 {
                    ArrayList<Circle> sorted = (ArrayList<Circle>) circles.clone();
                    Collections.sort(sorted, CircleRadiusComparator.getDescendingInstance());
                    // We create a triangle from the 3 circles
                    // so that the centers of the 3 circles are at the 3 corners
                    // of the triangle, and the circles touch each other.
                    // If the triangle connecting the three centres is acute, the
                    // smallest bounding circle is the outer circle tangent to all 
                    // three enclosing circles. This circle is known as the outer
                    // Soddy circle. When the triangle is obtuse, the bounding circle
                    //is the circle enclosing two largest circles. 


                    // Step 1: construct a triangle using the 3 circles
                    // ------------
                    // The circles form the three corners of a triangle:
                    // the largest one on the left, the second larges on the right
                    // the smallest one at the bottom. The circles are touching each
                    // other.
                    Circle ca = sorted.get(0);
                    Circle cb = sorted.get(1);
                    Circle cc = sorted.get(2);

                    // compute the side lengths of the thriangle which has
                    // its corners in the center of each circle.
                    double a = cb.radius + cc.radius;
                    double b = ca.radius + cc.radius;
                    double c = ca.radius + cb.radius;

                    // compute the height rc
                    double area = Math.sqrt(ca.radius * cb.radius * cc.radius * (ca.radius + cb.radius + cc.radius));
                    double hc = 2 * area / c;

                    ca.cx = -ca.radius;
                    ca.cy = 0;
                    cb.cx = cb.radius;
                    cb.cy = 0;
                    cc.cx = ca.cx + Math.sqrt(b * b - hc * hc);
                    cc.cy = hc;
                }
                break;
            case 4:
                 {
                    ArrayList<Circle> sorted = (ArrayList<Circle>) circles.clone();
                    Collections.sort(sorted, CircleRadiusComparator.getDescendingInstance());
                    // We create a triangle from the 3 PhylloNode circles
                    // so that the centers of the 3 circles are at the 3 corners
                    // of the triangle, and the circles touch each other.
                    // If the triangle connecting the three centres is acute, the
                    // smallest bounding circle is the outer circle tangent to all 
                    // three enclosing circles. This circle is known as the outer
                    // Soddy circle. When the triangle is obtuse, the bounding circle
                    //is the circle enclosing two largest circles. 


                    // Step 1: construct a triangle using the 3 PhylloNode circles
                    // ------------
                    // The circles of the PhylloNodes form the three corners of a triangle:
                    // the largest one on the left, the second larges on the right
                    // the smallest one at the bottom. The circles are touching each
                    // other.
                    Circle ca = sorted.get(0);
                    Circle cb = sorted.get(1);
                    Circle cc = sorted.get(2);

                    // compute the side lengths of the thriangle which has
                    // its corners in the center of each circle.
                    double a = cb.radius + cc.radius;
                    double b = ca.radius + cc.radius;
                    double c = ca.radius + cb.radius;

                    // compute the height rc
                    double area = Math.sqrt(ca.radius * cb.radius * cc.radius * (ca.radius + cb.radius + cc.radius));
                    double hc = 2 * area / c;

                    ca.cx = -ca.radius;
                    ca.cy = 0;
                    cb.cx = cb.radius;
                    cb.cy = 0;
                    cc.cx = ca.cx + Math.sqrt(b * b - hc * hc);
                    cc.cy = hc;

                    // compute the height rc'
                    cc = sorted.get(3);
                    b = ca.radius + cc.radius;
                    area = Math.sqrt(ca.radius * cb.radius * cc.radius * (ca.radius + cb.radius + cc.radius));
                    hc = 2 * area / c;

                    cc.cx = ca.cx + Math.sqrt(b * b - hc * hc);
                    cc.cy = -hc;
                }
                break;
            default:
                 {

                    ArrayList<Circle> sorted = (ArrayList<Circle>) circles.clone();
                    Collections.sort(sorted, CircleRadiusComparator.getDescendingInstance());

                    // only 10 percent difference between largest and smallest circle?
                    // lay out circles in a phyllotactic spiral
                    if (sorted.get(0).getRadius() <= sorted.get(sorted.size() - 1).getRadius() * 1.1) {
                        double c = Math.max(0.1, sorted.get(sorted.size() - 1).radius * 1.25);
                        for (int i = 0, m = sorted.size(); i < m; i++) {
                            Circle circle = sorted.get(i);
                            double cr = c * Math.sqrt(i + 1);
                            double ct = (i + 1) * 137.5 * Math.PI / 180d;

                            circle.cx = cr * Math.sin(ct);
                            circle.cy = cr * Math.cos(ct);
                        }
                    } else {
                        double c = Math.max(0.1, sorted.get(sorted.size() - 1).radius * 1.25);
                        for (int i = 0, m = sorted.size(); i < m; i++) {
                            Circle circle = sorted.get(i);
                            double cr = c * Math.sqrt(i + 1);
                            double ct = (i + 1) * 137.5 * Math.PI / 180d;

                            circle.cx = cr * Math.sin(ct);
                            circle.cy = cr * Math.cos(ct);
                        }
                        boolean intersects = false;
                        int iteration = 0;
                        do {
                            intersects = false;
                            for (int i = 0, m = sorted.size(); i < m; i++) {
                                Circle ci = sorted.get(i);
                                for (int j = i + 1; j < m; j++) {
                                    Circle cj = sorted.get(j);
                                    double dist2 = ((ci.cx - cj.cx) * (ci.cx - cj.cx) +
                                            (ci.cy - cj.cy) * (ci.cy - cj.cy));
                                    double requiredDist = ci.radius + cj.radius;
                                    if (dist2 < requiredDist * requiredDist) {
                                        double dist = Math.sqrt(dist2);
                                        double theta = Math.atan2(cj.cy, cj.cx);
                                        //double theta = Math.atan2(ci.cy - cj.cy, ci.cx - cj.cx);
                                        //double theta = Math.atan2(cj.cy - ci.cy, cj.cx - ci.cx);
                                        double dx = (requiredDist - dist + .01) * Math.cos(theta);
                                        double dy = (requiredDist - dist + .01) * Math.sin(theta);
                                        cj.cx += dx;
                                        cj.cy += dy;
                                        intersects = true;
                                    }
                                }
                            }
                            iteration++;
                        } while (intersects && iteration < 100);
                    }
                }
                break;
        }
    }

    /**
     * Packs circles closely together into a circle around the center of
     * the coordinate system by creating a list of already packed pairs of
     * circles.
     * <p>
     * The following algorithm is used:
     * <ol>
     * <li>Sort the circles from largest to smallest.</li>
     * <li>Arrange the first three circles in a triangle with corners A, B, C.</li>
     * <li>Create a list of 6 pairs for the 3 edges of the triangle: A-B, B-C, C-A,
     * B-A, C-B, A-C</li>
     * <li>For each remaining circle: try out all possible triangle arrangements
     * with the available pairs. Among the arrangements for which the circle
     * does not overlap with existing circles, choose the one, which places
     * the circle closest to the center of the first triangle. Add 4 pairs
     * for the two new triangle edges we have found to the pair list.</li>
     * </ol>
     * @param circles
     */
    public static void pairPack(ArrayList<Circle> circles) {
        double error = 0.01;
        
        switch (circles.size()) {
            case 0:
                break;
            case 1:
                 {
                    Circle circle = circles.get(0);
                    circle.cx = 0;
                    circle.cy = 0;
                }
                break;
            case 2:
                 {
                    Circle c0 = circles.get(0);
                    Circle c1 = circles.get(1);
                    double radius = c0.radius + c1.radius;
                    c0.cx = c0.radius - radius;
                    c1.cx = radius - c1.radius;
                    c0.cy = c1.cy = 0;
                }
                break;
            case 4 :
                {
                    // special treatment if we have four circles which
                    // are of roughly the same size
                    ArrayList<Circle> sorted = (ArrayList<Circle>) circles.clone();
                    Collections.sort(sorted, CircleRadiusComparator.getDescendingInstance());
                    if (sorted.get(0).radius / sorted.get(3).radius < 1.3) {
                    Circle c0 = sorted.get(0);
                    Circle c1 = sorted.get(1);
                    Circle c2 = sorted.get(2);
                    Circle c3 = sorted.get(3);
                    c0.cx = c0.cy = -c0.radius;
                    c1.cx = c1.cy = c1.radius;
                    c2.cx = c2.radius;
                    c2.cy = -c2.radius;
                    c3.cx = -c3.radius;
                    c3.cy = c3.radius;
                        break;
                    } else {
                        // fall through
                    }
                }
            default:
                 {
                    ArrayList<Circle> sorted = (ArrayList<Circle>) circles.clone();
                    Collections.sort(sorted, CircleRadiusComparator.getDescendingInstance());
                    // 1. We start with three circles tightly packed into a triangle.
                    // 2. We create a pairs list consisting of the three circles
                    // on the triangle.
                    // 3. With each remaining circle, we iterate through the
                    // pairs list, in order to find the closest location to
                    // the center of the original triangle, where the circle
                    // does not intersects with existing circles on the pairs
                    // list.


                    // Step 1: construct a triangle using the 3 circles
                    // ------------
                    // The circles form the three corners of a triangle:
                    // the largest one on the left, the second larges on the right
                    // the smallest one at the bottom. The circles are touching each
                    // other.
                    Circle ca = sorted.get(0);
                    Circle cb = sorted.get(1);
                    Circle cc = sorted.get(2);

                    // compute the side lengths of the triangle which has
                    // its corners in the center of each circle.
                    double a = cb.radius + cc.radius;
                    double b = ca.radius + cc.radius;
                    double c = ca.radius + cb.radius;

                    // compute the height rc
                    double area = Math.sqrt(ca.radius * cb.radius * cc.radius * (ca.radius + cb.radius + cc.radius));
                    double hc = 2 * area / c;

                    ca.cx = -ca.radius;
                    ca.cy = 0;
                    cb.cx = cb.radius;
                    cb.cy = 0;
                    cc.cx = ca.cx + Math.sqrt(b * b - hc * hc);
                    cc.cy = hc;
                    Point2D.Double cp = new Point2D.Double();
                    AffineTransform transform = new AffineTransform();

                    double shift = (ca.radius - cb.radius);
                    ca.cx += shift;
                    cb.cx += shift;
                    cc.cx += shift;



                    if (sorted.size() > 3) {
                        double smallestRadius = sorted.get(sorted.size() - 1).radius;

                        ArrayList<Pair> pairs = new ArrayList<Pair>();
                        pairs.add(new Pair(cb, ca)); // outer edges
                        pairs.add(new Pair(ca, cc));
                        pairs.add(new Pair(cc, cb));

                        double innerSoddyRadius = innerSoddyRadius(ca.radius, cb.radius, cc.radius);
                        if (innerSoddyRadius >= smallestRadius) {
                            pairs.add(new Pair(ca, cb, innerSoddyRadius)); // inner pair
                            pairs.add(new Pair(cc, ca, innerSoddyRadius)); // inner pair
                            pairs.add(new Pair(cb, cc, innerSoddyRadius)); // inner pair
                        }

                        Point2D.Double closestPoint = new Point2D.Double();
                        int closestEdgeIndex = -1;
                        Pair closestEdge = null;
                        for (int i = 3; i < sorted.size(); i++) {
                            cc = sorted.get(i);
                            closestPoint.x = Double.MAX_VALUE;
                            closestPoint.y = Double.MAX_VALUE;
                            closestEdgeIndex = -1;
                            closestEdge = null;
                            for (int pairIndex = 0; pairIndex < pairs.size(); pairIndex++) {
                                boolean intersects;
                                Pair pair = pairs.get(pairIndex);
                                if (pair.innerSoddyRadius < cc.radius -error) {
                                    intersects = true;
                                } else {

                                    ca = pair.ca;
                                    cb = pair.cb;

                                    // compute the side lengths of the triangle which has
                                    // its corners in the center of each circle.
                                    a = cb.radius + cc.radius;
                                    b = ca.radius + cc.radius;
                                    c = ca.radius + cb.radius;

                                    // compute the height rc
                                    area = Math.sqrt(ca.radius * cb.radius * cc.radius * (ca.radius + cb.radius + cc.radius));
                                    hc = 2 * area / c;

                                    cp.x = Math.sqrt(b * b - hc * hc);
                                    cp.y = hc;
                                    double theta = Math.atan2(cb.cy - ca.cy, cb.cx - ca.cx);
                                    transform.setToIdentity();
                                    transform.translate(ca.cx, ca.cy);
                                    transform.rotate(theta);
                                    transform.transform(cp, cp);
                                    // if we are farther away than the
                                    // closest point we found so far,
                                    // we can immediately abort intersection
                                    // tests.
                                    if (cp.x * cp.x + cp.y * cp.y >=
                                            closestPoint.x * closestPoint.x + closestPoint.y * closestPoint.y) {
                                        intersects = true;
                                    } else {
                                        intersects = false;
                                        cc.cx = cp.x;
                                        cc.cy = cp.y;

                                        for (int j = 0; j < i; j++) {
                                            if (cc.intersects(sorted.get(j), error)) {
                                                // make the inner soddy radius smaller, because we can't fit 
                                                // our circle in here
                                                pair.innerSoddyRadius = cc.getIntersectionRadius(sorted.get(j));
                                                intersects = true;
                                                break;
                                            }
                                        }
                                    }
                                }
                                if (!intersects) {
                                    if (cc.cx * cc.cx + cc.cy * cc.cy < closestPoint.x * closestPoint.x + closestPoint.y * closestPoint.y) {
                                        closestPoint.x = cc.cx;
                                        closestPoint.y = cc.cy;
                                        closestEdgeIndex = pairIndex;
                                        closestEdge = pairs.get(closestEdgeIndex);
                                    }
                                }
                            }
                            cc.cx = closestPoint.x;
                            cc.cy = closestPoint.y;
                            ca = pairs.get(closestEdgeIndex).ca;
                            cb = pairs.get(closestEdgeIndex).cb;
                            innerSoddyRadius = innerSoddyRadius(ca.radius, cb.radius, cc.radius);
                            if (innerSoddyRadius >= smallestRadius) {
                                pairs.get(closestEdgeIndex).innerSoddyRadius = innerSoddyRadius;
                                pairs.add(new Pair(cc, ca, innerSoddyRadius));
                                pairs.add(new Pair(cb, cc, innerSoddyRadius));
                            } else {
                                pairs.remove(closestEdgeIndex);
                            }
                            pairs.add(new Pair(ca, cc));
                            pairs.add(new Pair(cc, cb));
                        }
                    }
                }

                break;
        }
    }

    /**
     * Computes the radius of the inner soddy circle for three tightly packed
     * circles.
     * 
     * @param ra Radius of circle A
     * @param rb Radius of circle B
     * @param rc Radius of circle C
     * @return radius of the inner soddy circle
     */
    public static double innerSoddyRadius(double ra, double rb, double rc) {
        return (ra * rb * rc) / (ra * rc + ra * rb + rb * rc + Math.sqrt(4 * ra * rb * rc * (ra + rb + rc)));

    }

    /**
     * Computes the radius of the outer soddy circle for three tightly packed
     * circles.
     * 
     * @param ra Radius of circle A
     * @param rb Radius of circle B
     * @param rc Radius of circle C
     * @return radius of the outer soddy circle
     */
    public static double outerSoddyRadius(double ra, double rb, double rc) {
        /*
        // Solution using Descartes' theorem,
        // as described here: http://en.wikipedia.org/wiki/Descartes%27_theorem
        double k1,k2,k3,k4a,k4b;
        k1 = 1/ra;
        k2 = 1/rb;
        k3 = 1/rc;
        //k4a = Math.abs(k1+k2+k3+2*Math.sqrt(k1*k2+k2*k3+k3*k1));
        k4b = Math.abs(k1+k2+k3-2*Math.sqrt(k1*k2+k2*k3+k3*k1));
        return 1/k4b;
         */

        // Shorter solution:
        return Math.abs((ra * rb * rc) / (ra * rc + ra * rb + rb * rc - Math.sqrt(4 * ra * rb * rc * (ra + rb + rc))));
    }

    /**
     * Computes the circumradius of the reference triangle for three tightly packed
     * circles.
     * 
     * @param ra Radius of circle A
     * @param rb Radius of circle B
     * @param rc Radius of circle C
     * @return circumradius of the reference triangle.
     */
    public static double circumradius(double ra, double rb, double rc) {
        double a = rb + rc;
        double b = ra + rc;
        double c = ra + rb;

        double r = (a * b * c) /
                Math.sqrt((a + b + c) * (b + c - a) * (c + a - b) * (a + b - c));

        return r;
    }

    /**
     * Computes the outer soddy circle for three tightly packed
     * circles.
     * 
     * @param circleA Circle ra
     * @param circleB Circle rb
     * @param circleC Circle rc
     * @return Outer soddy circle. The Outer soddy circle has a radius
     * of 0, if there is no solution, that is, if the outer soddy circle
     * is a straight line.
     */
    public static Circle outerSoddyCircle(Circle circleA, Circle circleB, Circle circleC) {
        // radii of the three tightyl packed circles
        double ra = circleA.radius;
        double rb = circleB.radius;
        double rc = circleC.radius;

        // Solution using Descartes' theorem,
        // as described here: http://en.wikipedia.org/wiki/Descartes%27_theorem
        double k1, k2, k3, k4;
        k1 = 1 / ra;
        k2 = 1 / rb;
        k3 = 1 / rc;
        k4 = Math.abs(k1 + k2 + k3 - 2 * Math.sqrt(k1 * k2 + k2 * k3 + k3 * k1));
        Complex q1, q2, q3, q4;
        q1 = new Complex(k1, 0).mul(new Complex(circleA.cx, circleA.cy));
        q2 = new Complex(k2, 0).mul(new Complex(circleB.cx, circleB.cy));
        q3 = new Complex(k3, 0).mul(new Complex(circleC.cx, circleC.cy));
        q4 = q1.add(q2).add(q3).sub(new Complex(2, 0).mul(q1.mul(q2).add(q2.mul(q3)).add(q3.mul(q1)).sqrt()));

        Complex z = q4.div(new Complex(k4, 0));
        
        // if the formula is not solveable, we return an empty circle.
        // we compute the second solution.
        if (z.isNaN() || Double.isNaN(1/k4)) {
            return new Circle();
            /*
        k4 = Math.abs(k1 + k2 + k3 + 2 * Math.sqrt(k1 * k2 + k2 * k3 + k3 * k1));
        q4 = q1.add(q2).add(q3).add(new Complex(2,0).mul(q1.mul(q2).add(q2.mul(q3)).add(q3.mul(q1)).sqrt()));
        z = q4.div(new Complex(k4, 0));
             */
        }
        return new Circle(-z.real(), -z.img(), 1 / k4);
    }
    
    public static void main(String[] arg) {
        Circle a,b,c;
        a= new Circle(1.4210854715202004E-14,-54.162200020584606,18.0540666735282);
        b= new Circle(-72.2162666941128,0.0,72.2162666941128);
        c= new Circle(72.2162666941128,0.0,72.2162666941128);
        System.out.println("C:"+outerSoddyCircle(a, b, c));
        
        a= new Circle(-3.552713678800501E-15,-31.842677395339436,18.0540666735282);
        b= new Circle(36.09065056202983,-32.9661700825705,18.0540666735282);
        c= new Circle(-36.090650562029836,-32.9661700825705,18.0540666735282);
        System.out.println("B:"+outerSoddyCircle(a, b, c));
        
        System.out.flush();
    }

    private static class Pair {

        public Circle ca;
        public Circle cb;
        public double innerSoddyRadius = Double.MAX_VALUE;

        public Pair(Circle ca, Circle cb) {
            this.ca = ca;
            this.cb = cb;
        }

        public Pair(Circle ca, Circle cb, double innerSoddyRadius) {
            this.ca = ca;
            this.cb = cb;
            this.innerSoddyRadius = innerSoddyRadius;
        }
    }
}

