package src.utilities;

import java.util.StringTokenizer;

public class StringHelper {

	public static boolean isWhitespace(String line) {
		for(int i=0; i<line.length(); i++) {
			if(!Character.isWhitespace(line.charAt(i))) {
				return false;
			}
		}
		return true;
	}

	public static String removeWhitespace(String s) {

		StringTokenizer strtok = new StringTokenizer(s," ");
		String result = "";

		while(strtok.hasMoreTokens()) {
			result = result + strtok.nextToken();
		}

		return result;

	}
	
	public static String trimWhitespace(String s) {
		int beginNonWhitespace;
		int endNonWhitespace;
		
		for(beginNonWhitespace = 0; beginNonWhitespace < s.length() && Character.isWhitespace(s.charAt(beginNonWhitespace)); beginNonWhitespace++);

		if(beginNonWhitespace==s.length()) {
			return "";
		}
		
		for(endNonWhitespace = s.length(); endNonWhitespace > 0 && Character.isWhitespace(s.charAt(endNonWhitespace-1)); endNonWhitespace--);

		return s.substring(beginNonWhitespace,endNonWhitespace);
	}
	
	
	public static String nautyToGap(String nautyGenerators) {
		if(nautyGenerators=="") {
			return "Group(());";
		}
			
		String result = "Group(";
		StringTokenizer elementSplitter = new StringTokenizer(nautyGenerators,"\n");
		while (elementSplitter.hasMoreTokens()) {
			StringTokenizer cycleSplitter = new StringTokenizer(elementSplitter
					.nextToken(), "()");
			while (cycleSplitter.hasMoreTokens()) {
				result = result + "(";
				StringTokenizer numberSplitter = new StringTokenizer(
						cycleSplitter.nextToken(), " ");
				while (numberSplitter.hasMoreTokens()) {
					result = result
							+ (Integer.parseInt(numberSplitter.nextToken()) + 1);
					if (numberSplitter.hasMoreTokens())
						result = result + ",";
				}
				result = result + ")";
			}
			if (elementSplitter.hasMoreTokens())
				result = result + ",";
		}
		result = result + ")";
		return result;
	}		
	
	public static String gapToNauty(String gapGenerators) {
		String result = "";
		StringTokenizer strtok = new StringTokenizer(gapGenerators, "!\n");
		while (strtok.hasMoreTokens()) {
			result = result + gapToNautyPerm(strtok.nextToken())
					+ "\n";
		}
		return result;
	}
		
	public static String gapToNautyPerm(String gapPerm) {
		String result = "";
		StringTokenizer strtok = new StringTokenizer(gapPerm, "()");
		while (strtok.hasMoreTokens()) {
			result = result + "(";
			StringTokenizer strtok2 = new StringTokenizer(strtok.nextToken(),
					" ,");
			while (strtok2.hasMoreTokens()) {
				result = result + (Integer.parseInt(strtok2.nextToken()) - 1);
				if (strtok2.hasMoreTokens())
					result = result + " ";
			}
			result = result + ")";
		}

		return result;
	}

	public static String doubleUpSlashes(String common) {
		// For some reason, PERL interprets '\' as '\\' and vice-versa.
		// This method converts al '\' characters to '\\'.
		String result = "";
		for(int i=0; i<common.length(); i++) {
			if(common.charAt(i)=='\\') {
				result += "\\\\";
			} else {
				result += common.charAt(i);
			}
		}
		return result;
	}
}
