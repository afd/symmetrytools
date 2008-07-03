package src.etch.types;

import java.util.ArrayList;
import java.util.List;

import src.etch.checker.Checker;


import junit.framework.TestCase;

public class TypeTest extends TestCase {

	public void testNameOfRecursiveType() throws Exception {

		ProductType pt = null;
		ChanType root = new ChanType(pt);
		
		List<Type> tuple3 = new ArrayList<Type>();
		tuple3.add(root);
		tuple3.add(new IntType());
		
		List<Type> tuple2 = new ArrayList<Type>();
		tuple2.add(new ChanType(tuple3));
		tuple2.add(new IntType());
		
		List<Type> tuple1 = new ArrayList<Type>();
		tuple1.add(new ChanType(tuple2));
		tuple1.add(new IntType());
		
		root.setMessageType(Checker.theFactory.generateProductType(tuple1));

		System.out.println(root.name());
		
		System.out.println(Minimiser.minimise(root).name());

		
		List<Type> tuple4 = new ArrayList<Type>();
		tuple4.add(null); tuple4.add(null);
		
		ProductType pt2 = Checker.theFactory.generateProductType(tuple4);
		
		List<Type> tuple5 = new ArrayList<Type>();
		tuple5.add(new ChanType(pt2));
		tuple5.add(new IntType());
		
		pt2.setTypeOfPosition(0,new ChanType(Checker.theFactory.generateProductType(tuple5)));
		pt2.setTypeOfPosition(1,new IntType());
		ChanType root2 = new ChanType(pt2);
		
		System.out.println(root2.name());
		
		System.out.println(Minimiser.minimise(root2).name());
		
		
		
		List<Type> newTuple = new ArrayList<Type>();
		newTuple.add(null); newTuple.add(null); newTuple.add(null);
		
		ProductType pt3 = Checker.theFactory.generateProductType(newTuple);
		ChanType ct = new ChanType(pt3);
		
		pt3.setTypeOfPosition(0,ct);
		pt3.setTypeOfPosition(1,ct);
		pt3.setTypeOfPosition(2,ct);
		
		System.out.println(ct.name());
		
		pt3.setTypeOfPosition(2,root2);
		
		System.out.println(ct.name());
		
		System.out.println(Minimiser.minimise(ct).name());

		System.out.println(Checker.theFactory.generateByteType().name());

		System.out.println(Minimiser.minimise(Checker.theFactory.generateByteType()).name());

	}
	
	
}
