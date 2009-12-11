package at.logic.prooftool;

import java.util.Map;
import javax.swing.*;
import java.awt.*;
import java.awt.geom.*;
import org.jgraph.*;
import org.jgraph.graph.*;
import org.jgrapht.ext.JGraphModelAdapter;

public class ProofViewer {

    private GraphModel model = null;
    private GraphLayoutCache view = null;
    private JGraph graph = null;
    private JFrame frame = null;

    public ProofViewer() {
        this.model = new DefaultGraphModel();
        this.view = new GraphLayoutCache(model, new DefaultCellViewFactory());
        this.graph = new JGraph(model, view);



        frame = new JFrame();
        frame.getContentPane().add(new JScrollPane(graph));
        frame.pack();
        //frame.setVisible(true);
    }

    public ProofViewer(at.logic.utils.ds.graphs.Graph s) {
        JGraphModelAdapter adapter = new JGraphModelAdapter(s.getGraph());
        this.model = adapter;
        this.view = new GraphLayoutCache(model, new DefaultCellViewFactory());
        this.graph = new JGraph(model, view);

        frame = new JFrame();
        frame.getContentPane().add(new JScrollPane(graph));
        frame.pack();
    }


    public void insertLotsOfCells() {
        DefaultGraphCell[] morecells = new DefaultGraphCell[10000];

        for (int i = 0; i < morecells.length; i++) {
            //graph.getGraphLayoutCache().insert(new DefaultGraphCell("Vertex "+i));
            morecells[i] = new DefaultGraphCell("Vertex+i");
            GraphConstants.setBounds(morecells[i].getAttributes(), new Rectangle2D.Double((50 * i) % 1000, (i / 1000) * 30, 40, 20));
        }

        graph.getGraphLayoutCache().insert(morecells);
    }

    public void run() {
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

    public void setModel(GraphModel model) {
        this.model = model;
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

        //model.

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
                GraphConstants.setBounds(amap, new Rectangle2D.Double(60*(i%width), 40*(i/width), 40, 20));
                GraphConstants.setGradientColor(amap, Color.yellow);
                GraphConstants.setOpaque(amap, true);
                cache.editCell(cell, amap);
                i++;
            }
        }
        
    }

    
    // --- main method for testing ----
    public static void main(String[] args) {
        try {
            ProofViewer v = new ProofViewer();
            v.run();
            Thread.sleep(15000);
        } catch (Exception e) {
            //do nothing
        }
    }



        /*
        DefaultGraphCell[] cells = new DefaultGraphCell[3];
        cells[0] = new DefaultGraphCell(new String("Hello"));
        GraphConstants.setBounds(cells[0].getAttributes(), new Rectangle2D.Double(20,20,40,20));
        GraphConstants.setGradientColor(cells[0].getAttributes(), Color.orange);
        GraphConstants.setOpaque(cells[0].getAttributes(), true);

        DefaultPort port0 = new DefaultPort();
        cells[0].add(port0);
        cells[1] = new DefaultGraphCell(new String("World"));

        GraphConstants.setBounds(cells[1].getAttributes(), new Rectangle2D.Double(140, 140, 40, 20));
        GraphConstants.setGradientColor(cells[1].getAttributes(), Color.red);
        GraphConstants.setOpaque(cells[1].getAttributes(), true);


        DefaultPort port1 = new DefaultPort();
        cells[1].add(port1);
        DefaultEdge edge = new DefaultEdge();
        edge.setSource(cells[0].getChildAt(0));
        edge.setTarget(cells[1].getChildAt(0));
        cells[2] = edge;

        int arrow = GraphConstants.ARROW_CLASSIC;
        GraphConstants.setLineEnd(edge.getAttributes(), arrow);
        GraphConstants.setEndFill(edge.getAttributes(), true);
        graph.getGraphLayoutCache().insert(cells);
         */

}
