package src.lazyspinfrontend;

import src.etch.checker.Checker;
import src.etch.typeinference.ConstraintSet;
import src.symmextractor.PidSensitiveUnifier;
import src.symmextractor.types.SymmExtractorTypeFactory;

public class LazySpinRepGenerator extends Checker {

	public LazySpinRepGenerator() {
		super(new SymmExtractorTypeFactory(), new ConstraintSet(new PidSensitiveUnifier()));
	}

	
	
}
