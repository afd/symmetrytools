package src.symmreducer;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import junit.framework.Assert;

import src.etch.env.ChannelEntry;
import src.etch.env.EnvEntry;
import src.etch.env.ProctypeEntry;
import src.etch.env.TypeEntry;
import src.etch.env.VarEntry;
import src.etch.types.ArrayType;
import src.etch.types.ByteType;
import src.etch.types.ChanType;
import src.etch.types.PidType;
import src.etch.types.ProductType;
import src.etch.types.RecordType;
import src.etch.types.Type;
import src.symmextractor.StaticChannelDiagramExtractor;

public abstract class SymmetryApplier {

	protected StaticChannelDiagramExtractor typeInfo;

	public SymmetryApplier(StaticChannelDiagramExtractor typeInfo) {
		this.typeInfo = typeInfo;
	}

	protected int proctypeId(String proctypeName) {
		return typeInfo.getProctypeNames().indexOf(proctypeName);
	}

	protected List<PidIndexedArrayReference> getSensitivelyIndexedArrayReferences(String name, Type type, String referencePrefix) {

		List<PidIndexedArrayReference> result = new ArrayList<PidIndexedArrayReference>();
		if(isArray(type)) {
			if(isPid(((ArrayType)type).getIndexType()) && !isByte(((ArrayType)type).getIndexType())) {
				result.add(new PidIndexedArrayReference(referencePrefix + name,(ArrayType)type));
			}
			for(int i=0; i<((ArrayType)type).getLength(); i++) {
				result.addAll(getSensitivelyIndexedArrayReferences(name+"["+i+"]",((ArrayType)type).getElementType(),referencePrefix));
			}			
		} else if(isRecord(type)) {
			TypeEntry recordEntry = (TypeEntry)typeInfo.getEnvEntry(((RecordType)type).name()); 
			for(Iterator iter = recordEntry.getFieldNames().iterator(); iter.hasNext();) {
				String fieldName = (String)iter.next();
				result.addAll(getSensitivelyIndexedArrayReferences(fieldName,recordEntry.getFieldType(fieldName),referencePrefix+name+"."));
			}
		}
	
		return result;
	}

	protected List<SensitiveVariableReference> getSensitiveVariableReferences(String varName, Type varType, String prefix) {
		List<SensitiveVariableReference> result = new ArrayList<SensitiveVariableReference>();
		if(isPid(varType)||isChan(varType)) {
			result.add(new SensitiveVariableReference(prefix+varName,varType));
		} else if(isArray(varType)) {
			for(int i=0; i<((ArrayType)varType).getLength(); i++) {
				result.addAll(getSensitiveVariableReferences(varName+"["+i+"]",((ArrayType)varType).getElementType(),prefix));
			}
		} else if(isRecord(varType)) {
			TypeEntry typeEntry = (TypeEntry)typeInfo.getEnvEntry(((RecordType)varType).name());
			for(Iterator iter = typeEntry.getFieldNames().iterator(); iter.hasNext();) {
				String fieldName = (String)iter.next();
				result.addAll(getSensitiveVariableReferences(fieldName,typeEntry.getFieldType(fieldName),prefix+varName+"."));
			}
		}
	
		return result;
	}

	protected List<String> getInsensitiveVariableReferences(String varName, Type varType, String prefix) {
		List<String> result = new ArrayList<String>();
		
		if(isPid(varType)||isChan(varType)) {
			return result;
		}

		if(isArray(varType)) {
			if(isPid(((ArrayType)varType).getIndexType())) {
				return result;
			}

			for(int i=0; i<((ArrayType)varType).getLength(); i++) {
				result.addAll(getInsensitiveVariableReferences(varName+"["+i+"]",((ArrayType)varType).getElementType(),prefix));
				return result;
			}
		}
		
		if(isRecord(varType)) {
			TypeEntry typeEntry = (TypeEntry)typeInfo.getEnvEntry(((RecordType)varType).name());
			for(Iterator iter = typeEntry.getFieldNames().iterator(); iter.hasNext();) {
				String fieldName = (String)iter.next();
				result.addAll(getInsensitiveVariableReferences(fieldName,typeEntry.getFieldType(fieldName),prefix+varName+"."));
			}
			return result;
		}					
	
		result.add(prefix + varName);
		return result;

	}

	protected void writeMarkers(FileWriter fw) throws IOException {
		String markerStruct = "#define bitvector uchar\n#define SET_1(bv,i) bv=bv|(1<<i)\n\ntypedef struct Marker {\n";
		String markMethod = "void mark(Marker *marker, State* s, int i) {\n";
		
		Map<String,EnvEntry> globalVariables = typeInfo.getEnv().getTopEntries();
		for(Iterator<String> iter = globalVariables.keySet().iterator(); iter.hasNext();) {
			String name = iter.next();
			EnvEntry entry = globalVariables.get(name);
			if((entry instanceof VarEntry) && !(((VarEntry)entry).isHidden()||entry instanceof ChannelEntry)) {
				
				Type entryType = ((VarEntry)entry).getType();

				Assert.assertFalse(entryType instanceof ChanType);
				Assert.assertFalse(entryType instanceof ProductType);
				
				if(entryType instanceof ArrayType) {
					Assert.assertFalse(((ArrayType)entryType).getElementType() instanceof ChanType);
					Assert.assertFalse(((ArrayType)entryType).getElementType() instanceof ArrayType);
					Assert.assertFalse(((ArrayType)entryType).getElementType() instanceof ProductType);

					if(((ArrayType)entryType).getElementType() instanceof RecordType) {
						System.out.println("Markers do not currently support arrays of records");
						System.exit(0);
					}

					if(((ArrayType)entryType).getIndexType() instanceof PidType) {
						if(((ArrayType)entryType).getElementType() instanceof PidType) {
							System.out.println("Markers do not currently support arrays from pid to pid");
							System.exit(0);
						} else {
							markerStruct+="   uchar " + name + ";\n";
							markMethod += "   marker->" + name + " = s->" + name + "[i];\n";
						}
  					} else {
						Assert.assertTrue(((ArrayType)entryType).getIndexType() instanceof ByteType);
						if(((ArrayType)entryType).getElementType() instanceof PidType) {
							markerStruct+="   bitvector " + name + ";\n";
							markMethod += "   marker->"+name + "=0;\n";
							for(int i=0; i<((ArrayType)entryType).getLength(); i++) {
								markMethod  +="   if(s->"+name + "[" + i + "]==i) SET_1(marker->"+name+","+i+");\n";
							}
						}
					}
					
				} else if(entryType instanceof PidType) {
					markerStruct += "   uchar " + name + " : 1;\n";
					markMethod +=   "   marker->"+name+" = s->"+name+"==i ? 1 : 0;\n";
				} else if(entryType instanceof RecordType) {
					System.out.println("Markers do not currently support records");
					System.exit(0);
				}
				
			}
		}

		Assert.assertEquals(typeInfo.getProctypeNames().size(),2);

		Assert.assertEquals(typeInfo.getProctypeNames().get(1),ProctypeEntry.initProctypeName);

		String proctypeName = typeInfo.getProctypeNames().get(0);
		ProctypeEntry proctype = (ProctypeEntry) typeInfo.getEnvEntry(proctypeName);
		Map<String,EnvEntry> localScope = proctype.getLocalScope();
		markerStruct += "   uchar _p;\n";
        markMethod +=   "   marker->_p = ((P"+proctypeId(proctypeName)+" *)SEG(s,i))->_p;\n";
		
		for(Iterator<String> iter = localScope.keySet().iterator(); iter.hasNext();) {
			String varName = iter.next();
			if(localScope.get(varName) instanceof VarEntry) {
				Type entryType = ((VarEntry)localScope.get(varName)).getType();
				Assert.assertFalse(entryType instanceof ProductType);
				if(entryType instanceof ArrayType) {
					System.out.println("Local array variables not yet supported with markers");
					System.exit(0);
				}
				if(entryType instanceof RecordType) {
					System.out.println("Local record variables not yet supported with markers");
					System.exit(0);
				}

				if(entryType instanceof PidType) {
					System.out.println("Local pid variables not yet supported with markers");
					System.exit(0);
				} else {
					markerStruct += "   uchar " + varName + ";\n";
			        markMethod +=   "   marker->" + varName + " = ((P"+proctypeId(proctypeName)+" *)SEG(s,i))->" + varName + ";\n";
				}
			}
			
		}
		
		markerStruct += "} Marker;\n\n";
		markMethod += "}\n\n";
		
		fw.write(markerStruct);
		fw.write(markMethod);
	}

	private boolean isRecord(Type varType) {
		return varType instanceof RecordType;
	}

	private boolean isArray(Type varType) {
		return varType instanceof ArrayType;
	}

	protected boolean isChan(Type varType) {
		return varType instanceof ChanType;
	}

	protected static boolean isPid(Type varType) {
		return varType instanceof PidType;
	}

	private static boolean isByte(Type varType) {
		return varType instanceof ByteType;
	}

	
}
