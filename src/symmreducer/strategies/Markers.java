package src.symmreducer.strategies;

import java.io.FileWriter;
import java.io.IOException;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import junit.framework.Assert;
import src.etch.env.ChannelEntry;
import src.etch.env.EnvEntry;
import src.etch.env.ProctypeEntry;
import src.etch.env.VarEntry;
import src.etch.types.ArrayType;
import src.etch.types.ByteType;
import src.etch.types.ChanType;
import src.etch.types.ProductType;
import src.etch.types.RecordType;
import src.etch.types.VisibleType;
import src.symmextractor.StaticChannelDiagramExtractor;
import src.symmextractor.types.PidType;
import src.symmreducer.SensitiveVariableReference;
import src.utilities.Config;
import src.utilities.Strategy;

public class Markers {

	public static void writeMarkers(FileWriter out, StaticChannelDiagramExtractor typeInfo) throws IOException {
		String markerStruct = "#define bitvector unsigned int\n#define SET_1(bv,i) bv=bv|(1<<i)\n\ntypedef struct Marker {\n";
		String markMethod = "void mark(Marker *marker, State* s, int i) {\n   int j;\n";
		String eqMethod = "int eq(Marker* m1, Marker* m2) {\n   return ";
		String ltMarkersMethod = "int lt_markers(Marker* m1, Marker* m2) {\n";
		String ltMethod = "int lt(Marker* markers, int i, int j, State* s) {\n" +
			"if(lt_markers(&markers[i],&markers[j])) return 1;\n" + 
			"if(lt_markers(&markers[j],&markers[i])) return 0;\n\n";
		
		Map<String, EnvEntry> globalVariables = typeInfo.getGlobalVariables();
		for (String name : globalVariables.keySet()) {
			EnvEntry entry = globalVariables.get(name);
			if ((entry instanceof VarEntry)
					&& !(((VarEntry) entry).isHidden() || entry instanceof ChannelEntry)) {
	
				VisibleType entryType = ((VarEntry) entry).getType();
	
				Assert.assertFalse(entryType instanceof ChanType);
				Assert.assertFalse(entryType instanceof ProductType);
	
				if (entryType instanceof ArrayType) {
					Assert
							.assertFalse(((ArrayType) entryType)
									.getElementType() instanceof ChanType);
					Assert
							.assertFalse(((ArrayType) entryType)
									.getElementType() instanceof ArrayType);
					Assert
							.assertFalse(((ArrayType) entryType)
									.getElementType() instanceof ProductType);
	
					if (((ArrayType) entryType).getElementType() instanceof RecordType) {
						System.out
								.println("Markers do not currently support arrays of records");
						System.exit(0);
					}
	
					if (((ArrayType) entryType).getIndexType() instanceof PidType) {
						if (((ArrayType) entryType).getElementType() instanceof PidType) {
	
							
							markerStruct += "   uchar " + name + ";\n";
							eqMethod = appendEq(name, eqMethod);
							ltMarkersMethod = appendLt(name, ltMarkersMethod);
	
							markerStruct += "   uchar " + name + "_selfloop;\n";
							eqMethod = appendEq(name + "_selfloop", eqMethod);
							ltMarkersMethod = appendLt(name + "_selfloop", ltMarkersMethod);
	
							markMethod += "   marker->" + name + " = 0;\n";
							markMethod += "   for(j=1; j<" + typeInfo.getNoProcesses()
									+ "; j++) {\n";
							markMethod += "      if(s->" + name + "[j]==i) marker->"
									+ name + "++;\n";
							markMethod += "   }\n";
							markMethod += "   if(s->" + name + "[i]==i) marker->"
									+ name + "_selfloop = 1; else marker->"
									+ name + "_selfloop = 0;\n";
							
							ltMethod += "   if(s->" + name + "[i+1]==0) {\n" +
								"      if(s->" + name + "[j+1]!=0) { return 1; }\n" +
								"   } else {" +
								"      if(lt_markers(&markers[s->" + name + "[i+1]-1],&markers[s->" + name + "[j+1]-1])) return 1;\n" +
								"      if(lt_markers(&markers[s->" + name + "[j+1]-1],&markers[s->" + name + "[i+1]-1])) return 0;\n  }\n\n";

							// TODO Need to add this code for local pid variables too.  Don't think we need it for non-pid arrays or non-pid locals.
							
						} else {
							markerStruct += "   uchar " + name + ";\n";
							eqMethod = appendEq(name, eqMethod);
							ltMarkersMethod = appendLt(name, ltMarkersMethod);
							markMethod += "   marker->" + name + " = s->"
									+ name + "[i];\n";
						}
					} else {
						Assert.assertTrue(((ArrayType) entryType)
								.getIndexType() instanceof ByteType);
						if (((ArrayType) entryType).getElementType() instanceof PidType) {
							markerStruct += "   bitvector " + name + ";\n";
							eqMethod = appendEq(name, eqMethod);
							ltMarkersMethod = appendLt(name, ltMarkersMethod);
							markMethod += "   marker->" + name + "=0;\n";
							for (int i = 0; i < ((ArrayType) entryType)
									.getLength(); i++) {
								markMethod += "   if(s->" + name + "[" + i
										+ "]==i) SET_1(marker->" + name + ","
										+ i + ");\n";
							}
						}
					}
	
				} else if (entryType instanceof PidType) {
					markerStruct += "   uchar " + name + " : 1;\n";
					eqMethod = appendEq(name, eqMethod);
					ltMarkersMethod = appendLt(name, ltMarkersMethod);
					markMethod += "   marker->" + name + " = s->" + name
							+ "==i ? 1 : 0;\n";
				} else if (entryType instanceof RecordType) {
					System.out
							.println("Markers do not currently support records");
					System.exit(0);
				}
	
			}
		}
	
		Assert.assertEquals(typeInfo.getProctypeNames().size(), 2);
	
		Assert.assertEquals(typeInfo.getProctypeNames().get(1),
				ProctypeEntry.initProctypeName);
	
		String proctypeName = typeInfo.getProctypeNames().get(0);
		ProctypeEntry proctype = (ProctypeEntry) typeInfo
				.getEnvEntry(proctypeName);
		Map<String, EnvEntry> localScope = proctype.getLocalScope();
		eqMethod = appendEq("_p", eqMethod);
		ltMarkersMethod = appendLt("_p", ltMarkersMethod);
		markerStruct += "   uchar _p;\n";
		markMethod += "   marker->_p = ((P" + typeInfo.proctypeId(proctypeName)
				+ " *)SEG(s,i))->_p;\n";
	
		for (String varName : localScope.keySet()) {
			if (localScope.get(varName) instanceof VarEntry) {
				VisibleType entryType = ((VarEntry) localScope.get(varName)).getType();
				Assert.assertFalse(entryType instanceof ProductType);
				if (entryType instanceof ArrayType) {
					System.out
							.println("Local array variables not yet supported with markers");
					System.exit(0);
				}
				if (entryType instanceof RecordType) {
					System.out
							.println("Local record variables not yet supported with markers");
					System.exit(0);
				}
	
				if (entryType instanceof PidType) {
					markerStruct += "   uchar " + varName + ";\n";
					eqMethod = appendEq(varName, eqMethod);
					ltMarkersMethod = appendLt(varName, ltMarkersMethod);
	
					markerStruct += "   uchar " + varName + "_selfloop;\n";
					eqMethod = appendEq(varName + "_selfloop", eqMethod);
					ltMarkersMethod = appendLt(varName + "_selfloop", ltMarkersMethod);
	
					markMethod += "   marker->" + varName + " = 0;\n";
					markMethod += "   for(j=1; j<" + typeInfo.getNoProcesses()
							+ "; j++) {\n";
					markMethod += "      if(((P" + typeInfo.proctypeId(proctypeName)
							+ " *)SEG(s,j))->" + varName + "==i) marker->"
							+ varName + "++;\n";
					markMethod += "   }\n";
					markMethod += "   if(((P" + typeInfo.proctypeId(proctypeName)
							+ " *)SEG(s,i))->" + varName + "==i) marker->"
							+ varName + "_selfloop = 1; else marker->"
							+ varName + "_selfloop = 0;\n";
				} else {
					markerStruct += "   uchar " + varName + ";\n";
					eqMethod = appendEq(varName, eqMethod);
					ltMarkersMethod = appendLt(varName, ltMarkersMethod);
					markMethod += "   marker->" + varName + " = ((P"
							+ typeInfo.proctypeId(proctypeName) + " *)SEG(s,i))->"
							+ varName + ";\n";
				}
			}
	
		}
	
		List<String> staticChannelNames = typeInfo.getStaticChannelNames();
		int chanId = 0;
		for (String chanName : staticChannelNames) {
			ProductType msgType = (ProductType) ((ChanType) ((ChannelEntry) typeInfo
					.getEnvEntry(chanName)).getType()).getMessageType();
			int chanLength = ((ChannelEntry) typeInfo.getEnvEntry(chanName))
					.getLength();
			for (int i = 0; i < msgType.getArity(); i++) {
				Assert.assertTrue(msgType.getTypeOfPosition(i) instanceof VisibleType);
				VisibleType fieldType = (VisibleType) msgType.getTypeOfPosition(i);
	
				Assert.assertFalse(fieldType instanceof ArrayType); // SPIN
				// doesn't
				// allow
				// this
	
				if (fieldType instanceof RecordType) {
					System.out
							.println("Record fields on channels not yet supported with markers");
					System.exit(0);
				}
	
				if (fieldType instanceof PidType) {
					markerStruct += "   bitvector " + chanName + "_fld" + i
							+ ";\n";
					eqMethod = appendEq(chanName + "_fld" + i, eqMethod);
					ltMarkersMethod = appendLt(chanName + "_fld" + i, ltMarkersMethod);
				}
				markMethod += "   marker->" + chanName + "_fld" + i + "=0;\n";
				for (int j = 0; j < chanLength; j++) {
					markMethod += "   if( ((Q" + (chanId + 1) + "*)QSEG(s,"
							+ chanId + "))->contents[" + j + "].fld" + i
							+ "==i) SET_1(marker->" + chanName + "_fld" + i
							+ "," + j + ");\n";
				}
	
			}
			chanId++;
	
		}
	
		markerStruct += "} Marker;\n\n";
		markMethod += "}\n\n";
		ltMarkersMethod += "   return 0;\n}\n\n";
		/* Get rid of trailing && from eqMethod */
		eqMethod = eqMethod.substring(0, eqMethod.length() - 2) + ";\n}\n\n";
	
		ltMethod += "    return 0;\n\n}\n\n";
		
		out.write(markerStruct);
		out.write(markMethod);
		out.write(ltMarkersMethod);
		out.write(eqMethod);
		out.write(ltMethod);
		
		if (Config.REDUCTION_STRATEGY == Strategy.APPROXMARKERS) {
			writeMarkPID(out, typeInfo);
		}

	}

	private static void writeMarkPID(FileWriter fw, StaticChannelDiagramExtractor typeInfo) throws IOException {
		Map<String, EnvEntry> globalVariables = typeInfo.getGlobalVariables();

		String referencePrefix = "s->";

		fw.write("void markPIDs(State* s, int* map) {\n");

		for (Iterator<String> iter = globalVariables.keySet().iterator(); iter
				.hasNext();) {
			String name = iter.next();
			EnvEntry entry = globalVariables.get(name);
			if ((entry instanceof VarEntry)
					&& !(((VarEntry) entry).isHidden() || entry instanceof ChannelEntry)) {
				List sensitiveReferences = SensitiveVariableReference.getSensitiveVariableReferences(name,
						((VarEntry) entry).getType(), referencePrefix, typeInfo);
				for (int i = 0; i < sensitiveReferences.size(); i++) {
					SensitiveVariableReference reference = (SensitiveVariableReference) sensitiveReferences
							.get(i);
					Assert.assertTrue(PidType.isPid(reference.getType()));
					fw.write("   if(" + reference + ">0) "
							+ reference + " = map["
							+ reference + "-1]+1;\n");
				}
			}
		}
		
		String proctypeName = typeInfo.getProctypeNames().get(0);
		ProctypeEntry proctype = (ProctypeEntry) typeInfo
				.getEnvEntry(proctypeName);
		Map<String, EnvEntry> localScope = proctype.getLocalScope();
		for (String varName : localScope.keySet()) {
			if (localScope.get(varName) instanceof VarEntry) {
				VisibleType entryType = ((VarEntry) localScope.get(varName)).getType();
				Assert.assertFalse(entryType instanceof ProductType);
				if (entryType instanceof PidType) {
					for (int j = 1; j < typeInfo.getNoProcesses(); j++) {
						fw.write("   if(((P" + typeInfo.proctypeId(proctypeName)
								+ " *)SEG(s," + j + "))->" + varName + ">0) "
								+ "((P" + typeInfo.proctypeId(proctypeName)
								+ " *)SEG(s," + j + "))->" + varName
								+ " = map[ " + "((P" + typeInfo.proctypeId(proctypeName)
								+ " *)SEG(s," + j + "))->" + varName
								+ "-1]+1;\n");
					}
				}
			}

		}

		List<String> staticChannelNames = typeInfo.getStaticChannelNames();
		int chanId = 0;
		for (String chanName : staticChannelNames) {
			ProductType msgType = (ProductType) ((ChanType) ((ChannelEntry) typeInfo
					.getEnvEntry(chanName)).getType()).getMessageType();
			int chanLength = ((ChannelEntry) typeInfo.getEnvEntry(chanName))
					.getLength();
			for (int i = 0; i < msgType.getArity(); i++) {
				Assert.assertTrue(msgType.getTypeOfPosition(i) instanceof VisibleType);
				VisibleType fieldType = (VisibleType) msgType.getTypeOfPosition(i);

				Assert.assertFalse(fieldType instanceof ArrayType); // SPIN
				// doesn't
				// allow
				// this

				if (fieldType instanceof PidType) {
					for (int j = 0; j < chanLength; j++) {
						fw.write("   if(((Q" + (chanId + 1) + "*)QSEG(s,"
								+ chanId + "))->contents[" + j + "].fld" + i
								+ ">0) " + "((Q" + (chanId + 1) + "*)QSEG(s,"
								+ chanId + "))->contents[" + j + "].fld" + i
								+ "=map[((Q" + (chanId + 1) + "*)QSEG(s,"
								+ chanId + "))->contents[" + j + "].fld" + i
								+ "-1]+1;\n");
					}
				}
			}
			chanId++;
		}
		
		/* NOW SWAP AROUND THE pid-indexed ARRAYS */

		fw.write("   uchar swapper[" + typeInfo.getNoProcesses() + "];\n");
		fw.write("   swapper[0] = 0;\n");
		fw.write("   int i;\n");
		
		for (Iterator<String> iter = globalVariables.keySet().iterator(); iter
			.hasNext();) {
			String name = iter.next();
			EnvEntry entry = globalVariables.get(name);
			if ((entry instanceof VarEntry)
					&& !(((VarEntry) entry).isHidden() || entry instanceof ChannelEntry)) {
				if(((VarEntry)entry).getType() instanceof ArrayType && ((ArrayType)((VarEntry)entry).getType()).getIndexType() instanceof PidType) {
					fw.write("   for(i=1; i<" + typeInfo.getNoProcesses() + "; i++) swapper[i]=0;\n\n");
					
					for(int i=1; i<typeInfo.getNoProcesses(); i++) {
						fw.write("   swapper[map[" + (i-1) + "]+1] = s->" + name + "[" + i + "];\n");
					}

					fw.write("   memcpy(s->" + name + ",swapper," + typeInfo.getNoProcesses() + ");\n\n");
				
				}
			}
		}
			
		
		fw.write("}\n\n");

	}
	
	
	private static String appendEq(String name, String eqMethod) {
		return eqMethod + "(m1->" + name + "==m2->" + name + ")&&";
	}

	private static String appendLt(String name, String ltMarkersMethod) {
		return ltMarkersMethod + "   if(m1->" + name + "<m2->" + name
				+ ") return 1;\n   if(m1->" + name + ">m2->" + name
				+ ") return 0;\n";
	}

	private static void writeRepApproxMarkers(FileWriter out, final int procsminus1) throws IOException {
		out.write("   Marker markers[" + procsminus1 + "], orig_markers["
				+ procsminus1 + "], temp;\n");
		out.write("   State tempstate;\n");
		out.write("   int i, j, map[" + procsminus1 + "];\n\n");
		out.write("   memcpy(&min_now,orig_now,vsize);\n");
		out.write("   for(i=0; i<" + procsminus1 + "; i++) {\n");
		out.write("      mark(&markers[i],orig_now,i+1);\n");
		out.write("   }\n\n");
		out.write("   memcpy(orig_markers,markers," + procsminus1
				+ "*sizeof(Marker));\n\n");
		out.write("   for(i=0; i<" + (procsminus1 - 1) + "; i++) {\n");
		out.write("      for(j=i+1; j<" + procsminus1 + "; j++) {\n");
		out.write("         if(lt(markers,i,j,orig_now)) {\n");
		out.write("            memcpy(&temp,&markers[i],sizeof(Marker));\n");
		out.write("            memcpy(&markers[i],&markers[j],sizeof(Marker));\n");
		out.write("            memcpy(&markers[j],&temp,sizeof(Marker));\n");
		out.write("         }\n");
		out.write("      }\n");
		out.write("   }\n\n");
		out.write("   for(i=0; i<" + procsminus1 + "; i++) {\n");
		out.write("      for(j=" + (procsminus1 - 1) + "; j>=0; j--) {\n");
		out.write("         if(eq(&markers[j],&orig_markers[i])) {\n");
					/* Check the next one....find the smallest */
		out.write("            map[i] = j;\n");
		out.write("            break;\n");
		out.write("         }\n");
		out.write("      }\n");
		out.write("   }\n\n");
		out.write("   markPIDs(&min_now,map);\n");
	}

	private static void writeRepExactMarkers(FileWriter out, int procsminus1) throws IOException {
		out.write("   Marker markers[" + procsminus1 + "], temp;\n");
		out.write("   int i, j;\n");
		out.write("   memcpy(&min_now,orig_now,vsize);\n");
		out.write("   for(i=0; i<" + procsminus1 + "; i++) {\n");
		out.write("      mark(&markers[i],orig_now,i+1);\n");
		out.write("   }\n");
		out.write("   for(i=0; i<" + (procsminus1 - 1) + "; i++) {\n");
		out.write("      for(j=i+1; j<" + procsminus1 + "; j++) {\n");
		out.write("         if(lt(markers,i,j,orig_now)) {\n");
		out.write("            memcpy(&temp,&markers[i],sizeof(Marker));");
		out.write("            memcpy(&markers[i],&markers[j],sizeof(Marker));\n");
		out.write("            memcpy(&markers[j],&temp,sizeof(Marker));\n");
		out.write("            applyPrSwapToState(&min_now,i+1,j+1);\n");
		out.write("         }\n");
		out.write("      }\n");
		out.write("   }\n");
	}

	public static void writeRepFunction(StaticChannelDiagramExtractor typeInfo, FileWriter out) throws IOException {
		int procsminus1 = typeInfo.getNoProcesses() - 1;
		// FOR SIMPLICITY, I HAVE INCLUDED DUPLICATE CODE FOR
		// EACH MARKERS STRATEGY.
		if (Config.REDUCTION_STRATEGY == Strategy.EXACTMARKERS) {
			writeRepExactMarkers(out, procsminus1);
		} else if (Config.REDUCTION_STRATEGY == Strategy.APPROXMARKERS) {
			writeRepApproxMarkers(out, procsminus1);
		}		
	}
	
}
