package src.lazyspinfrontend;

import src.promela.analysis.DepthFirstAdapter;
import src.promela.node.AManyActive;
import src.promela.node.ANumberConst;
import src.promela.node.AOneActive;
import src.promela.node.AProctype;
import src.promela.node.PConst;

public class LazySpinFindNumProcesses extends DepthFirstAdapter {

	private boolean foundProctype = false;
	private int numProcesses;

	public int getNumProcesses() {
		return numProcesses;
	}
	
	@Override
	public void outAProctype(AProctype node) {
		
		if(foundProctype) {
			System.out.println("Error: multiple proctypes defined.");
			System.exit(1);
		}
		foundProctype = true;
		if(node.getActive() == null) {
			System.out.println("Error: proctype must be 'active'.");
			System.exit(1);
		}
		
		if(node.getActive() instanceof AOneActive) {
			numProcesses = 1;
		} else {
			PConst constant = ((AManyActive)node.getActive()).getConst();
			if(!(constant instanceof ANumberConst)) {
				System.out.println("Active proctype specifies non-numeric number of processes");
				System.exit(1);
			}

			if(null != ((ANumberConst)constant).getMinus()) {
				System.out.println("Active proctype specifies negative number of processes");
				System.exit(1);
			}
			
			numProcesses = Integer.parseInt(((ANumberConst)constant).getNumber().getText());
			
			if(numProcesses == 0) {
				System.out.println("Active proctype specifies zero process");
				System.exit(1);
			}
			
		}
					
	}
	
}
