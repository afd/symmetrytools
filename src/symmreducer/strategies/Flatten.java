package src.symmreducer.strategies;

import java.io.FileWriter;
import java.io.IOException;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;


import src.etch.env.ChannelEntry;
import src.etch.env.EnvEntry;
import src.etch.env.VarEntry;
import src.etch.types.ChanType;
import src.etch.types.VisibleType;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.symmextractor.types.PidType;
import src.symmreducer.SensitiveVariableReference;
import src.symmreducer.TypeFlattener;

public class Flatten {

	public static void writeFlatten(FileWriter fw, StaticChannelDiagramExtractor typeInfo) throws IOException {
		fw.write("void flatten(State *s) {\n");
		writeFlattenSensitiveGlobals(fw, typeInfo);
		writeFlattenSensitiveLocals(fw, typeInfo);
		writeFlattenSensitiveChannels(fw, typeInfo);
		fw.write("}\n\n");
	}

	private static void writeFlattenSensitiveChannels(FileWriter fw, StaticChannelDiagramExtractor typeInfo)
			throws IOException {
		for (int i = 0; i < typeInfo.getNoStaticChannels(); i++) {

			ChanType type = (ChanType) ((ChannelEntry) typeInfo
					.getEnvEntry((String) typeInfo.getStaticChannelNames().get(
							i))).getType();

			List<VisibleType> flattenedFieldTypes = TypeFlattener.flatten(type
					.getMessageType(), typeInfo);

			if (PidType.containsPidType(flattenedFieldTypes)
					|| ChanType.containsChanType(flattenedFieldTypes)) {
				fw.write("   for(slot=0; slot<((Q" + (i + 1) + " *)QSEG(s," + i
						+ "))->Qlen; slot++) {\n");

				for (int j = 0; j < flattenedFieldTypes.size(); j++) {
					if (PidType.isPid(flattenedFieldTypes.get(j))
							|| ChanType.isChan(flattenedFieldTypes.get(j))) {
						fw.write("      ((Q" + (i + 1) + " *)QSEG(s," + i
								+ "))->contents[slot].fld" + j + "=0;\n");
					}
				}
				fw.write("   }\n\n");
			}
		}
	}

	private static void writeFlattenSensitiveLocals(FileWriter fw, StaticChannelDiagramExtractor typeInfo) throws IOException {
		for (int j = 0; j < typeInfo.getProcessEntries().size(); j++) {

			for (ListIterator<SensitiveVariableReference> iter = typeInfo.sensitiveVariableReferencesForProcess(j).listIterator(); iter
					.hasNext();) {
				SensitiveVariableReference reference = (SensitiveVariableReference) iter
						.next();
				assert(PidType.isPid(reference.getType())
						|| ChanType.isChan(reference.getType()));
				fw.write("   " + reference + " = 0;\n");
			}

			fw.write("\n");
		}
	}

	private static void writeFlattenSensitiveGlobals(FileWriter fw, StaticChannelDiagramExtractor typeInfo) throws IOException {
		Map<String, EnvEntry> globalVariables = typeInfo.getGlobalVariables();

		String referencePrefix = "s->";

		for (Iterator<String> iter = globalVariables.keySet().iterator(); iter
				.hasNext();) {
			String name = iter.next();
			EnvEntry entry = globalVariables.get(name);
			if ((entry instanceof VarEntry)
					&& !(((VarEntry) entry).isHidden() || entry instanceof ChannelEntry)) {
				List<SensitiveVariableReference> sensitiveReferences = SensitiveVariableReference.getSensitiveVariableReferences(name,
						((VarEntry) entry).getType(), referencePrefix, typeInfo);
				for (int i = 0; i < sensitiveReferences.size(); i++) {
					SensitiveVariableReference reference = (SensitiveVariableReference) sensitiveReferences
							.get(i);
					assert(PidType.isPid(reference.getType()));
					fw.write("   " + reference + " = 0;\n");
				}
			}
		}
	}

}
