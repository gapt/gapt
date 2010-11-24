package at.logic.prooftool;

import java.util.Map;
import java.util.Set;
import javax.swing.*;
import java.awt.*;
import java.awt.geom.*;
import java.util.HashMap;
import org.jgraph.*;
import org.jgraph.graph.*;
import org.jgrapht.ext.JGraphModelAdapter;
import org.jgrapht.DirectedGraph;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.ListenableDirectedGraph;

public class ProofViewer<V> {

    private JGraphModelAdapter model = null;
//    private DefaultGraphModel model = null;
    private GraphLayoutCache view = null;
    private JGraph graph = null;
    private JFrame frame = null;
    private DirectedGraph<V, DefaultEdge> graph_data;

    public ProofViewer() {
        this.graph_data = new ListenableDirectedGraph<V, DefaultEdge>(DefaultEdge.class);
        this.model = new JGraphModelAdapter(graph_data);
        this.view = new GraphLayoutCache(model, new DefaultCellViewFactory());
        this.graph = new JGraph(model, view);

        frame = new JFrame();
        frame.getContentPane().add(new JScrollPane(graph));
        frame.pack();
    }

    /* --- removed with jgrapht support
    public ProofViewer(at.logic.utils.ds.graphs.Graph s) {
        JGraphModelAdapter adapter = new JGraphModelAdapter(s.getGraph());
        this.model = adapter;
        this.view = new GraphLayoutCache(model, new DefaultCellViewFactory());
        this.graph = new JGraph(model, view);
        this.graph_data = s.getGraph();

        frame = new JFrame();
        frame.getContentPane().add(new JScrollPane(graph));
        frame.pack();

    }
    */

    /*
    public void insertLotsOfCells(int number) {
        if (number < 1) {
            number = 1;
        }
        DefaultGraphCell[] morecells = new DefaultGraphCell[number];

        for (int i = 0; i < morecells.length; i++) {
            //graph.getGraphLayoutCache().insert(new DefaultGraphCell("Vertex "+i));
            morecells[i] = new DefaultGraphCell("Vertex " + i);
            GraphConstants.setBounds(morecells[i].getAttributes(), new Rectangle2D.Double((50 * i) % 1000, (i / 1000) * 30, 40, 20));
        }

        ConnectionSet cs = new ConnectionSet();
        org.jgraph.graph.DefaultEdge port = null;
        for (int i = 1; i < number; i++) {
            port = new org.jgraph.graph.DefaultEdge();
            if (i % 10 == 9) {
                cs.connect(morecells[0], morecells[i], false);
            } else {
                cs.connect(morecells[i - 1], morecells[i], false);
            }
        }

        //graph.getGraphLayoutCache().insert(morecells);
        model.beginUpdate();
        model.insert(morecells, null, cs, null, null);
        model.endUpdate();
    } */

    public void run() {
        /*
        this.frame.addWindowStateListener(new WindowStateListener() {
        public void windowStateChanged(WindowEvent arg0) {
        System.err.println("event:"+arg0);
        if (WindowEvent.WINDOW_CLOSING) {
        arg0.getWindow().setVisible(false);
        System.err.println("Closing...");

        }
        }
        })*/
        this.frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        this.frame.setVisible(true);
    }

    // ---- getters & setters ----
    public JFrame getFrame() {
        return frame;
    }

    public void setFrame(JFrame frame) {
        this.frame = frame;
    }

    public JGraph getGraph() {
        return graph;
    }

    public void setGraph(JGraph graph) {
        this.graph = graph;
    }

    public GraphModel getModel() {
        return model;
    }

    public void setModel(JGraphModelAdapter model) {
        this.model = model;
        this.graph = new JGraph(model);
    }

    public GraphLayoutCache getView() {
        return view;
    }

    public void setView(GraphLayoutCache view) {
        this.view = view;
    }

    // placement
    public void doPlacement() {
        GraphLayoutCache cache = this.graph.getGraphLayoutCache();
        Object[] cells = cache.getCells(false, true, false, false);


        DefaultGraphCell cell = null;
        AttributeMap amap = null;
        int i = 0;
        int width = (int) Math.floor(Math.abs(Math.sqrt(cells.length)));

        //this.model.
        for (Object o : cells) {
            //System.err.println(o);
            //System.err.println(o.getClass().getCanonicalName());
            if (o instanceof DefaultGraphCell) {
                cell = (DefaultGraphCell) o;
                amap = cell.getAttributes();
                GraphConstants.setBounds(amap, new Rectangle2D.Double(60 * (i % width), 40 * (i / width), 40, 20));
                GraphConstants.setGradientColor(amap, Color.yellow);
                GraphConstants.setOpaque(amap, true);
                cache.editCell(cell, amap);
                i++;
            }
        }

    }


    public Set<V> getChildren(V v) {
        Set<DefaultEdge> e = graph_data.outgoingEdgesOf(v);
        Set<V> r = new ListSet();
        for (DefaultEdge e_ : e) {
            r.add(graph_data.getEdgeTarget(e_));
        }
        return r;
    }

    public Integer depthOf(V v, Map<Integer, Set<V>> m) {
        for (Map.Entry<Integer, Set<V>> entry : m.entrySet()) {
            if (entry.getValue().contains(v)) {
                return entry.getKey();
            }
        }

        return -1;
    }

    public int getParentMean(V v, Map<DefaultGraphCell, AttributeMap> newmap) {
        Set<DefaultEdge> e = graph_data.incomingEdgesOf(v);
        if (e.size() == 0) {
            return 0;
        }
        AttributeMap amap = null;
        Rectangle2D rect = null;

        int x = 0;
        for (DefaultEdge e_ : e) {
            //amap = model.getVertexCell(graph_data.getEdgeTarget(e_)).getAttributes();
            amap = newmap.get(model.getVertexCell(graph_data.getEdgeSource(e_)));
            if (amap == null) {
                //TODO: find out why some vertices have no attribute map
                //System.err.println("amap null for" + v);
                continue;
            }
            rect = GraphConstants.getBounds(amap);
            x += rect.getX();
        }
        return x / e.size();
    }

    public void doTreePlacement() {
        /* assumption: edges are directed to the root */
        model.beginUpdate();
        //System.err.println("point 1");

        // find roots
        Set<V> slice = getRoots(graph_data);

        // separate nodes by the depth in the tree, the root is at level 0
        Map<Integer, Set<V>> slices = new HashMap<Integer, Set<V>>();
        Integer level = 0;
        slices.put(level, slice);
        Set<V> oldslice = null;
        Set<DefaultEdge > edges = null;
        Set<V> leaves = new ListSet<V>();

        while (slice.size() > 0) {
            level++;
            oldslice = slice;
            slice = new ListSet<V>();
            for (V v : oldslice) {
                edges = graph_data.incomingEdgesOf(v);
                if (edges.size() == 0) {
                    leaves.add(v);
                    continue;
                }

                for (DefaultEdge e : edges) {
                    slice.add(graph_data.getEdgeSource(e));
                }
            }

            slices.put(level, slice);
            //System.err.println("slice on level "+level+" with size "+slice.size());
        }


        Integer max_depth = level;

        Map m = new HashMap();
        DefaultGraphCell cell = null;
        AttributeMap amap = null;
        int leafx = 0;
        slice = new ListSet<V>();
        Rectangle2D.Double rect = null;

/*        int xsize = 60;
        int ysize = 20;
        int ystep = 50;
        int xstep = 100;
        */
        int xsize = 260;
        int ysize = 20;
        int ystep = 70;
        int xstep = 400;

        for (V v : leaves) {
            cell = model.getVertexCell(v);
            amap = cell.getAttributes();
            rect = new Rectangle2D.Double(leafx, 50 + ystep * (max_depth - depthOf(v, slices)), xsize, ysize);
            GraphConstants.setBounds(amap, rect);
            GraphConstants.setGradientColor(amap, Color.yellow);
            GraphConstants.setOpaque(amap, true);
            m.put(cell, amap);
            //System.err.println("leaf "+ cell+" at "+rect);
            leafx += xstep;

            slice.addAll(getChildren(v));
        }

        ConnectionSet cs = model.getConnectionSet();
        model.edit(m, cs, null, null);
        //oldslice = leaves;
        while (!slice.isEmpty()) {
            //System.err.println(slice.size()+" "+slice);
            oldslice = slice;
            slice = new ListSet<V>();
            for (V v : oldslice) {
                slice.addAll(getChildren(v));

                cell = model.getVertexCell(v);
                amap = cell.getAttributes();
                rect = new Rectangle2D.Double(getParentMean(v, m), 50 + ystep * (max_depth - depthOf(v, slices)), xsize, ysize);
                GraphConstants.setBounds(amap, rect);
                GraphConstants.setGradientColor(amap, Color.yellow);
                GraphConstants.setOpaque(amap, true);
                m.put(cell, amap);
            }
        }
        model.endUpdate();
    }


    public Set<V> getRoots(DirectedGraph<V, DefaultEdge> graph) {
        Set<V> vertices = graph.vertexSet();

        Set<V> slice = new ListSet<V>();
        for (V v : vertices) {
            if (graph.outDegreeOf(v) == 0) {
                slice.add(v);
                //System.err.println("root " + v );
            } else {
                //System.err.println("nonroot"+v);
            }

        }
        return slice;
    }

    // --- main method for testing ----
    public static void main(String[] args) {
        try {
            /*
            ProofViewer v = new ProofViewer();
            v.insertLotsOfCells(1000);
            v.doTreePlacement();
            v.run();
            //Thread.sleep(15000);*/
        } catch (Exception e) {
            //do nothing
            e.printStackTrace();
        }
    }
}
