package src.symmreducer;

import src.promela.node.ANever;
import src.promela.node.ANotraceTrace;
import src.promela.node.ATraceTrace;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.symmreducer.error.VerificationConstructNotSupportedError;

public class StaticChannelDiagramExtractorForSymmetryReduction extends
		StaticChannelDiagramExtractor {

	protected StaticChannelDiagramExtractorForSymmetryReduction() {
		super();
	}
	
	public void outANever(ANever node) {
		addError(node.getNevertok(), new VerificationConstructNotSupportedError(node.getNevertok()));	
		super.outANever(node);
	}

	public void outATraceTrace(ATraceTrace node) {
		addError(node.getTracetok(), new VerificationConstructNotSupportedError(node.getTracetok()));	
		super.outATraceTrace(node);
	}

	public void outANotraceTrace(ANotraceTrace node) {
		addError(node.getNotrace(), new VerificationConstructNotSupportedError(node.getNotrace()));	
		super.outANotraceTrace(node);
	}
	
}
