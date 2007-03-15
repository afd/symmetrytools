package src.symmreducer;

import java.util.Collections;
import java.util.Set;

public class VarInfo {
	private Set<String> pidVars;

	private Set<String> chanVars;

	public VarInfo(Set<String> pVars, Set<String> cVars) {
		pidVars = pVars;
		chanVars = cVars;
	}

	public Set<String> getPidVars() {
		return Collections.unmodifiableSet(pidVars);
	}

	public Set<String> getChanVars() {
		return Collections.unmodifiableSet(chanVars);
	}

	public boolean isEmpty() {
		return (pidVars.isEmpty() && chanVars.isEmpty());
	}

}
