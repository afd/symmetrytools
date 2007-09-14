package src.promela;

import junit.framework.Assert;
import src.promela.node.AFifoReceive;
import src.promela.node.AFifoRecvPoll;
import src.promela.node.AFifopollReceive;
import src.promela.node.ARandomReceive;
import src.promela.node.ARandomRecvPoll;
import src.promela.node.ARandompollReceive;
import src.promela.node.ARecordVarref;
import src.promela.node.ASingleVarref;
import src.promela.node.PReceive;
import src.promela.node.PRecvArgs;
import src.promela.node.PRecvPoll;
import src.promela.node.PVarref;
import src.promela.node.TName;

public class NodeHelper {

	public static TName getNameFromVaribableReference(PVarref node) {
		if(node instanceof ASingleVarref) {
			return ((ASingleVarref)node).getName();
		}
		return ((ARecordVarref)node).getName();
	}

	public static boolean hasArrayReference(PVarref node) {
		return ((node instanceof ASingleVarref && ((ASingleVarref)node).getArrayref() != null)
				|| (node instanceof ARecordVarref && ((ARecordVarref)node).getArrayref() != null));
	}

	public static PVarref getVariableReferenceFromReceiveStatement(PReceive node) {
		if(node instanceof AFifoReceive) {
			return ((AFifoReceive)node).getVarref();
		} else if(node instanceof AFifopollReceive) {
			return ((AFifopollReceive)node).getVarref();
		} else if(node instanceof ARandomReceive) {
			return ((ARandomReceive)node).getVarref();
		} else {
			Assert.assertTrue(node instanceof ARandompollReceive);
			return ((ARandompollReceive)node).getVarref();
		}
	}

	public static PVarref getVariableReferenceFromReceiveStatement(PRecvPoll node) {
		if(node instanceof AFifoRecvPoll) {
			return ((AFifoRecvPoll)node).getVarref();
		} else {
			Assert.assertTrue(node instanceof ARandomRecvPoll);
			return ((ARandomRecvPoll)node).getVarref();
		}
	}

	public static PRecvArgs getReceiveArgs(PReceive node) {
		if(node instanceof AFifoReceive) {
			return ((AFifoReceive)node).getRecvArgs();
		} else if(node instanceof AFifopollReceive) {
			return ((AFifopollReceive)node).getRecvArgs();
		} else if(node instanceof ARandomReceive) {
			return ((ARandomReceive)node).getRecvArgs();
		} else {
			Assert.assertTrue(node instanceof ARandompollReceive);
			return ((ARandompollReceive)node).getRecvArgs();
		}
	}

	public static PRecvArgs getRecevieArgs(PRecvPoll node) {
		if(node instanceof AFifoRecvPoll) {
			return ((AFifoRecvPoll)node).getRecvArgs();
		} else {
			Assert.assertTrue(node instanceof ARandomRecvPoll);
			return ((ARandomRecvPoll)node).getRecvArgs();
		}
	}	
}
