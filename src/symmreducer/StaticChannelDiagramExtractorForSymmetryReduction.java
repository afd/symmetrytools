package src.symmreducer;

import src.promela.node.ALabel;
import src.promela.node.ANever;
import src.promela.node.ANotraceTrace;
import src.promela.node.ATraceTrace;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.symmreducer.error.VerificationConstructNotSupportedError;
import src.utilities.StringHelper;

public class StaticChannelDiagramExtractorForSymmetryReduction extends
		StaticChannelDiagramExtractor {

	protected StaticChannelDiagramExtractorForSymmetryReduction() {
		super();
	}
	
	@Override
	public void outANever(ANever node) {
		addError(node.getNevertok(), new VerificationConstructNotSupportedError(node.getNevertok()));	
		super.outANever(node);
	}

	@Override
	public void outATraceTrace(ATraceTrace node) {
		addError(node.getTracetok(), new VerificationConstructNotSupportedError(node.getTracetok()));	
		super.outATraceTrace(node);
	}

	@Override
	public void outANotraceTrace(ANotraceTrace node) {
		addError(node.getNotrace(), new VerificationConstructNotSupportedError(node.getNotrace()));	
		super.outANotraceTrace(node);
	}
	
	@Override
	public void outALabel(ALabel node) {
		if(StringHelper.isAcceptLabelName(node.getName().getText()) || StringHelper.isProgressLabelName(node.getName().getText())) {
			addError(node.getName(), new VerificationConstructNotSupportedError(node.getName()));
		}
		super.outALabel(node);
	}
	
}
