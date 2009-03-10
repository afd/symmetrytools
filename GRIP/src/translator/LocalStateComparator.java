package src.translator;

import java.util.Comparator;
import java.util.List;

public class LocalStateComparator implements Comparator<List<Integer>> {

	public int compare(List<Integer> state1, List<Integer> state2) {
		//Assert.assertEquals(state1.size(),state2.size());
		
		for(int i=0; i<state1.size(); i++) {
			if(state1.get(i)>state2.get(i)) {
				return 1;
			} else if(state1.get(i)<state2.get(i)) {
				return -1;
			}
		}
		return 0;
	}

}
