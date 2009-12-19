package at.logic.prooftool;

import java.util.List;
import java.util.Set;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;

public class ListSet<T> implements Set<T> {

    private ArrayList<T> list = new ArrayList<T>();
    private class Comp implements Comparator<T> {
        @Override
        public int compare(T t1, T t2) {
            if (t1 == t2) return 0;
            if (t1 == null) return -1;
            if (t2 == null) return 1;

            int hc1 = t1.hashCode();
            int hc2 = t2.hashCode();
            if (hc1 == hc2) return 0;
            if (hc1<hc2) return -1;

            return 1;
        }
    }

    @Override
    public int hashCode() {
        if (list == null) return 0;
        HashSet s = new HashSet(list);
        return s.hashCode();
    }

    @Override
    public boolean equals(Object o) {
        if (o.hashCode() != this.hashCode()) return false;
        try {
            Set s1 = (Set) o;
            HashSet s2 = new HashSet(list);
            return s2.equals(s1);

        } catch (ClassCastException e) {
            return false;
        }
    }

    @Override
    public int size() {
        return list.size();
    }

    @Override
    public boolean isEmpty() {
        return list.isEmpty();
    }

    @Override
    public boolean contains(Object arg0) {
        return list.contains(arg0);
    }

    @Override
    public Iterator<T> iterator() {
        return list.iterator();
    }

    @Override
    public Object[] toArray() {
        return list.toArray();
    }

    @Override
    public <S> S[] toArray(S[] arg0) {
        return list.toArray(arg0);
    }

    @Override
    public boolean add(T arg0) {
        if (list.contains(arg0)) {
            return false;
        }
        list.add(arg0);
        return true;
    }

    @Override
    public boolean remove(Object arg0) {
        return list.remove(arg0);
    }

    @Override
    public boolean containsAll(Collection arg0) {
        return list.contains(arg0);
    }

    @Override
    public boolean addAll(Collection arg0) {
        return list.addAll(arg0);
    }

    @Override
    public boolean retainAll(Collection arg0) {
        return list.retainAll(arg0);
    }

    @Override
    public boolean removeAll(Collection arg0) {
        return list.removeAll(arg0);
    }

    @Override
    public void clear() {
        list.clear();
    }
}
