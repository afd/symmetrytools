package src.symmextractor;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import src.etch.checker.Checker;
import src.etch.env.ChannelEntry;
import src.etch.env.EnvEntry;
import src.etch.env.ProcessEntry;
import src.etch.env.ProctypeEntry;
import src.promela.node.AChannelIvarassignment;
import src.promela.node.AFifoReceive;
import src.promela.node.AFifoRecvPoll;
import src.promela.node.AFifoSend;
import src.promela.node.AFifopollReceive;
import src.promela.node.AInit;
import src.promela.node.AManyArgLst;
import src.promela.node.AOneArgLst;
import src.promela.node.AProctype;
import src.promela.node.ARandomReceive;
import src.promela.node.ARandomRecvPoll;
import src.promela.node.ARandompollReceive;
import src.promela.node.ARunFactor;
import src.promela.node.ASingleIvar;
import src.promela.node.ASortedSend;
import src.promela.node.PArgLst;
import src.promela.node.PIvar;
import src.promela.node.TSeparator;
import src.utilities.StringHelper;

public class StaticChannelDiagramExtractor extends Checker {
	
	protected List<ProcessEntry> processEntries = new ArrayList<ProcessEntry>();

	private List<String> staticChannelNames = new ArrayList<String>();

	protected List<String> proctypeNames = new ArrayList<String>();

	private Set<ChannelEntry> distinctChannelSignatures = new HashSet<ChannelEntry>();

	private List<Integer> colourPermutation;
	private List<Integer> colourPartition;

	private boolean inProctype = false;
	
	public StaticChannelDiagramExtractor() {
		super(true);
	}
	
	public List<String> getStaticChannelNames() {
		return Collections.unmodifiableList(staticChannelNames);
	}

	public int getNoStaticChannels() {
		return staticChannelNames.size();
	}

	public int proctypeId(String proctypeName) {
		return getProctypeNames().indexOf(proctypeName);
	}
	
	public Map<String, EnvEntry> getGlobalVariables() {
		return getEnv().getTopEntries();
	}
	
	public Set<ChannelEntry> getDistinctChannelSignatures() {
		return Collections.unmodifiableSet(distinctChannelSignatures);
	}
	
	public List<Integer> getColourPartition() {
		return Collections.unmodifiableList(colourPartition);
	}

	public void caseAInit(AInit node) {
		proctypeNames.add(ProctypeEntry.initProctypeName);
		processEntries.add(ProcessEntry.initProcess);
		super.caseAInit(node);
	}

	public void caseTSeparator(TSeparator node) {
		node.setText(";");
	}
	
	public String directedSaucyRepresentation() {
		
		List<Integer> edges = new ArrayList<Integer>();
		colourPartition = new ArrayList<Integer>();
		colourPermutation = new ArrayList<Integer>();

		for(int i=0; i<staticChannelNames.size() + processEntries.size(); i++) {
			colourPermutation.add(-1);
		}
		
		computeDistinctChannelSignatures();

		assignProcessColours();
		assignChannelColours();

		// EDGES
		for(ListIterator<ProcessEntry> li = processEntries.listIterator(); li.hasNext();) {
			ProcessEntry processEntry = li.next();

			addEdges(edges, processEntry,
					proctypeForProcess(processEntry),true);
			addEdges(edges, processEntry,
					proctypeForProcess(processEntry),false);
		}

		return constructSaucyOutput(edges);

	}

	private void computeDistinctChannelSignatures() {
		Map channelEntries = getEnv().getChannelEntries();
		for (Iterator iter = channelEntries.values().iterator(); iter.hasNext();) {
			addChannelEntry((ChannelEntry) iter.next());
		}
	}

	private String constructSaucyOutput(List edges) {
		// Number of nodes
		String result = (processEntries.size() + staticChannelNames.size())
				+ " ";

		// Number of edges. The array list edges stores each
		// pair of vertices as successive entries, so the number
		// of edges is the size of this list divided by 2.
		result = result + (edges.size() / 2) + " ";

		// Number of partitions of vertices. If the array
		// "partition" has no elements then there is 1 partition
		// so we need to add 1 to the size of partitions.
		result = result + (colourPartition.size() + 1) + " ";

		// Starting vertex of each partition
		for (int k = 0; k < colourPartition.size(); k++) {
			result = result + colourPartition.get(k) + " ";
		}

		// Edges
		for (int k = 0; k < edges.size(); k++) {
			result = result + edges.get(k) + " ";
		}
		
		return result;
	}

	private ProctypeEntry proctypeForProcess(ProcessEntry processEntry) {
		return (ProctypeEntry) getEnvEntry(processEntry.getProctypeName());
	}

	private void addEdges(List<Integer> edges, ProcessEntry processEntry, ProctypeEntry proctypeEntry, boolean outgoing) {
		
		Iterator<String> iter = (outgoing ? proctypeEntry.getOutChannels().iterator() : proctypeEntry.getInChannels().iterator());

		while(iter.hasNext()) {
			String chanName = iter.next();

			if (staticChannelNames.contains(chanName)) {
				if(outgoing) {
					edges.add(colourPermutation.get(processEntries.indexOf(processEntry)));
					edges.add(colourPermutation.get(staticChannelNames.indexOf(chanName) + processEntries.size()));
				} else {
					edges.add(colourPermutation.get(staticChannelNames.indexOf(chanName) + processEntries.size()));
					edges.add(colourPermutation.get(processEntries.indexOf(processEntry)));
				}
			}
			else {
				List argNames = proctypeEntry.getArgNames();
				for (int k = 0; k < argNames.size(); k++) {
					if (chanName.equals(argNames.get(k))) {

						int channelIndex = staticChannelNames.indexOf(processEntry.getParameterNames().get(k));
						
						if(outgoing) {
							edges.add(colourPermutation.get(processEntries.indexOf(processEntry)));
							edges.add(colourPermutation.get(channelIndex + processEntries.size()));
						} else {
							edges.add(colourPermutation.get(channelIndex + processEntries.size()));
							edges.add(colourPermutation.get(processEntries.indexOf(processEntry)));
						}
						break;
					}
				}
			}
		}
		
	}

	private void assignChannelColours() {
		int marker = colourPartition.get(colourPartition.size() - 1);

		for(Iterator<ChannelEntry> iter = distinctChannelSignatures.iterator(); iter.hasNext();) {
			ChannelEntry channelEntry = iter.next();
			ListIterator<String> j = staticChannelNames.listIterator();
			while (j.hasNext()) {
				String currentName = j.next();
				ChannelEntry currentEntry = (ChannelEntry)getEnvEntry(currentName);

				if (currentEntry.equal(channelEntry)) {
					colourPermutation.set(staticChannelNames.indexOf(currentName)
							+ processEntries.size(),marker);
					marker++;
				}
			}
			if (iter.hasNext()) {
				colourPartition.add(marker);
			}
		}
	}

	private void assignProcessColours() {
		int marker = 0;

		for(Iterator<String> i = proctypeNames.iterator(); i.hasNext();) {
			String proctypeName = i.next();
			for(ListIterator j = processEntries.listIterator(); j.hasNext();) {
				ProcessEntry currentProcessEntry = (ProcessEntry) j.next();
				if (currentProcessEntry.getProctypeName().equals(proctypeName)) {
					colourPermutation.set(processEntries
							.indexOf(currentProcessEntry),marker);
					marker++;
				}
			}
			if(i.hasNext() || !staticChannelNames.isEmpty()) {
				colourPartition.add(new Integer(marker));
			}
		}
	}

	public void caseAProctype(AProctype node) {
		inProctype = true;
		super.caseAProctype(node);
		proctypeNames.add(node.getName().getText());
		inProctype = false;
	}

	public void outARunFactor(ARunFactor node) {
		super.outARunFactor(node);

		List<String> parameterNames = new ArrayList<String>();

		PArgLst paramList = node.getArgLst();
		if (paramList != null) {
			while (paramList instanceof AManyArgLst) {
				parameterNames.add(StringHelper
						.removeWhitespace(((AManyArgLst) paramList).getExpr()
								.toString()));
				paramList = ((AManyArgLst) paramList).getArgLst();
			}
			parameterNames.add(StringHelper
					.removeWhitespace(((AOneArgLst) paramList).getExpr()
							.toString()));
		}
		processEntries.add(new ProcessEntry(node.getName().getText(),
				parameterNames));
	}

	public void outAChannelIvarassignment(AChannelIvarassignment node) {

		if(inTypedef) {
			// TODO DISOBEYING RESTRICTIONS
			System.out.println("Dynamic channel creation is not permitted when applying symmetry reduction, therefore channels cannot be initialised inside a user defined type. <useful message on how to remodel>");
			System.exit(0);
		}
		

		if(inProctype) {
			// TODO DISOBEYING RESTRICTIONS
			System.out.println("Dynamic channel creation is not permitted when applying symmetry reduction, therefore channels cannot be initialised inside a proctype. <useful message on how to remodel>");
			System.exit(0);
		}
		
		PIvar channel = (PIvar) node.parent();
		
		if (channel instanceof ASingleIvar) {
			staticChannelNames.add((((ASingleIvar) channel)).getName().getText());
		}

		else {
			// TODO DISOBEYING RESTRICTIONS
			System.out.println("Global arrays of channels are not permitted when applying symmetry reduction. <useful message on how to remodel>");
			System.exit(0);
		}
	}

	private void addChannelEntry(ChannelEntry channelEntry) {
		for (Iterator iter = distinctChannelSignatures.iterator(); iter.hasNext();) {
			if (channelEntry.equal((ChannelEntry) iter.next())) {
				return;
			}
		}
		distinctChannelSignatures.add(channelEntry);
	}

	public void outAFifoSend(AFifoSend node) {
		currentProctype.addOutChannelName(StringHelper.removeWhitespace(node
				.getVarref().toString()));
		super.outAFifoSend(node);
	}

	public void outASortedSend(ASortedSend node) {
		// There should be some kind of error as we can't have sorted sending.
		super.outASortedSend(node);
	}

	public void outAFifoReceive(AFifoReceive node) {
		currentProctype.addInChannelName(StringHelper.removeWhitespace(node
				.getVarref().toString()));
		super.outAFifoReceive(node);
	}

	public void outARandomReceive(ARandomReceive node) {
		// There should be an error
		super.outARandomReceive(node);
	}

	public void outAFifopollReceive(AFifopollReceive node) {
		currentProctype.addInChannelName(StringHelper.removeWhitespace(node
				.getVarref().toString()));
		super.outAFifopollReceive(node);
	}

	public void outARandompollReceive(ARandompollReceive node) {
		// There should be an error
		super.outARandompollReceive(node);
	}

	public void outAFifoRecvPoll(AFifoRecvPoll node) {
		currentProctype.addInChannelName(StringHelper.removeWhitespace(node
				.getVarref().toString()));
		super.outAFifoRecvPoll(node);
	}

	public void outARandomRecvPoll(ARandomRecvPoll node) {
		// There should be an error
		super.outARandomRecvPoll(node);
	}

	public String getScdNode(int i) {
		if(i<processEntries.size()) {
			return String.valueOf(i);
		}
		return staticChannelNames.get(i-processEntries.size());
	}

	public String getScdNodeForSaucyValue(int i) {
		return getScdNode(colourPermutation.indexOf(i));
	}
	
	public int getGapNumber(String s) {
		try {
			return Integer.parseInt(s);
		} catch(NumberFormatException e) {
			return staticChannelNames.indexOf((String)s) + processEntries.size();
		}
	}

	public int getNoProcesses() {
		return processEntries.size();
	}

	public List<String> getProctypeNames() {
		return Collections.unmodifiableList(proctypeNames);
	}

	public List<ProcessEntry> getProcessEntries() {
		return Collections.unmodifiableList(processEntries);
	}
	
	
}
