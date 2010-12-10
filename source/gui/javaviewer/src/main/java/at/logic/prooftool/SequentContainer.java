package at.logic.prooftool;

import java.awt.Color;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Rectangle;

import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JPanel;
import javax.swing.border.MatteBorder;


public class SequentContainer extends Box {
	private static final long serialVersionUID = 951334986686132912L;
	private Box upperbox = null;
	private Box lowerbox = null;
	private JPanel left = null;
	private JPanel right = null;
	private JPanel bottom = null;

	private Rectangle bounds = null;
	
	public SequentContainer() {
		super(BoxLayout.Y_AXIS);
		upperbox = new Box(BoxLayout.X_AXIS);
		lowerbox = new Box(BoxLayout.X_AXIS);
		left = new JPanel();
		right = new JPanel();
		bottom = new JPanel();
		
		this.add(upperbox);
		this.add(lowerbox);
		
		int vpadding = 10;
		int hpadding = 5;
		Color transparent = new Color(0,0,0,0);
		left.setBorder(  new MatteBorder(vpadding,hpadding,vpadding,hpadding, transparent));
		right.setBorder( new MatteBorder(vpadding,hpadding,vpadding,hpadding, transparent));
		bottom.setBorder(new MatteBorder(vpadding,hpadding,vpadding,hpadding, transparent));
		int bs = 5;
		upperbox.setBorder(new MatteBorder(bs,bs,bs,bs, transparent));
		lowerbox.setBorder(new MatteBorder(bs,bs,bs,bs, transparent));
		//this.setBorder(new MatteBorder(bs,bs,bs,bs, transparent));
		upperbox.add(left);
		upperbox.add(Box.createGlue());
		upperbox.add(Box.createRigidArea(new Dimension(100,0)));
		upperbox.add(right);
		lowerbox.add(Box.createGlue());
		lowerbox.add(bottom);
		lowerbox.add(Box.createGlue());
	}


	public JPanel getLeft() {
		return left;
	}


	public JPanel getRight() {
		return right;
	}


	public JPanel getBottom() {
		return bottom;
	}
	
	@Override
	public void paintComponent(Graphics g) {
		super.paintComponent(g);
		this.bounds = this.getBounds();
		int hr = this.upperbox.getHeight()+2;

		if ((left.getComponentCount()>0) && (right.getComponentCount()>0) &&
				(left.getComponent(0) instanceof SequentContainer) &&
				(right.getComponent(0) instanceof SequentContainer)) {
			SequentContainer lc = (SequentContainer) left.getComponent(0);
			SequentContainer rc = (SequentContainer) right.getComponent(0);
			int pl = lc.lowerbox.getComponent(0).getWidth();
			int pr = lc.lowerbox.getComponent(2).getWidth();
			g.drawLine(pl, hr, bounds.width-pr, hr);
			return;
		} 
		
		
		g.setColor(Color.black);
		int le = 5;
		int re = bounds.width-5;
		g.drawLine(le, hr, re, hr);
		
	}
	
}
