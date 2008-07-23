package src.etch.types;

import java.util.ArrayList;
import java.util.List;

import src.etch.checker.Checker;


import junit.framework.Assert;
import junit.framework.TestCase;

public class TypeTest extends TestCase {

	public TypeTest() {
		Checker.theFactory = new EtchTypeFactory();
	}
	
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

		Assert.assertEquals("rec X . chan { chan { chan { X, int }, int }, int }", root.name());
		
		Assert.assertEquals("rec X . chan { X, int }", Minimiser.minimise(root).name());
		
		List<Type> tuple4 = new ArrayList<Type>();
		tuple4.add(null); tuple4.add(null);
		
		ProductType pt2 = Checker.theFactory.generateProductType(tuple4);
		
		List<Type> tuple5 = new ArrayList<Type>();
		tuple5.add(new ChanType(pt2));
		tuple5.add(new IntType());
		
		pt2.setTypeOfPosition(0,new ChanType(Checker.theFactory.generateProductType(tuple5)));
		pt2.setTypeOfPosition(1,new IntType());
		ChanType root2 = new ChanType(pt2);
		
		Assert.assertEquals("chan rec X . { chan { chan X, int }, int }", root2.name());
		
		Assert.assertEquals("rec X . chan { X, int }", Minimiser.minimise(root2).name());
		
		List<Type> newTuple = new ArrayList<Type>();
		newTuple.add(null); newTuple.add(null); newTuple.add(null);
		
		ProductType pt3 = Checker.theFactory.generateProductType(newTuple);
		ChanType ct = new ChanType(pt3);
		
		pt3.setTypeOfPosition(0,ct);
		pt3.setTypeOfPosition(1,ct);
		pt3.setTypeOfPosition(2,ct);
		
		Assert.assertEquals("rec X . chan { X, X, X }", ct.name());
		
		pt3.setTypeOfPosition(2,root2);

		Assert.assertEquals("rec X . chan { X, X, chan rec Y . { chan { chan Y, int }, int } }", ct.name());

		Assert.assertEquals("rec X . chan { X, X, rec Y . chan { Y, int } }", Minimiser.minimise(ct).name());

		Assert.assertEquals("byte", Checker.theFactory.generateByteType().name());

		Assert.assertEquals("byte", Minimiser.minimise(Checker.theFactory.generateByteType()).name());

	}
	
	public void testNameOfArrayType() throws Exception {

		ArrayType t = new ArrayType(new MtypeType(), Checker.theFactory.generateByteType(), 25);
		
		Assert.assertEquals("array(size 25) of mtype", t.name());
				
	}

}
