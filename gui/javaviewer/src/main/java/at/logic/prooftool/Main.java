package at.logic.prooftool;

import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JScrollPane;


public class Main {
	static int count = 0;
	
	static SequentContainer genRec(int depth) {
		SequentContainer sc = new SequentContainer();;
		if (depth<=0) {
			 sc.getLeft().add(new JLabel("sequent "+count));
			 count++;
			 sc.getRight().add(new JLabel("sequent "+count));
			 count++;
			 sc.getBottom().add(new JLabel("sequent "+count));
			 count++;
			 return sc;
		}
		sc.getLeft().add(genRec(depth-1));
		sc.getRight().add(genRec(depth-1));
		sc.getBottom().add(new JLabel("sequent "+count));
		count++;
		return sc;
	}


	public static void main(String[] args) {
		javax.swing.SwingUtilities.invokeLater(new Runnable() {
			public void run() {
				try {
					JFrame frame = new JFrame("Swingyling");
					frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
					SequentContainer sc = new SequentContainer();
					sc.getLeft().add(new JLabel("left sequent"));
					sc.getRight().add(new JLabel("right sequent"));
					sc.getBottom().add(new JLabel("bottom sequent"));
					
					sc.setVisible(true);
					
					JScrollPane spane = new JScrollPane();
					spane.setViewportView(genRec(7));
					
					frame.getContentPane().add(spane);
					frame.pack();
					frame.setVisible(true);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		});
	}
}
