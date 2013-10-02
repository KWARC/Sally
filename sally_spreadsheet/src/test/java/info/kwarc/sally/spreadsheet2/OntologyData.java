package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.List;

public class OntologyData {
	
	OntologyFunctionObject plus, minus, equal,sum5, rev, expenses, profit;
	
	public OntologyData() {
		// omdoc://spsht-arith#plus
		List<String> arguments = new ArrayList<String>();
		arguments.add("omdoc://MathML#Real");
		arguments.add("omdoc://MathML#Real");
		
		List<String> vars = new ArrayList<String>();
		vars.add("x1");
		vars.add("x2");
		
		String mathML = "<apply><plus/><ci>x1</ci><ci>x2</ci></apply>";
		plus = new OntologyFunctionObject("omdoc://spsht-arith#plus", arguments, vars, "omdoc://MathML#Real", mathML);
	
		// omdoc://spsht-arith#minus
		arguments = new ArrayList<String>();
		arguments.add("omdoc://MathML#Real");
		arguments.add("omdoc://MathML#Real");
				
		vars = new ArrayList<String>();
		vars.add("x1");
		vars.add("x2");
				
		mathML = "<apply><minus/><ci>x1</ci><ci>x2</ci></apply>";
		minus = new OntologyFunctionObject("omdoc://spsht-arith#minus", arguments, vars, "omdoc://MathML#Real", mathML);
		
		// omdoc://spsht-arith#equal
		arguments = new ArrayList<String>();
		arguments.add("omdoc://MathML#Real");
		arguments.add("omdoc://MathML#Real");
				
		vars = new ArrayList<String>();
		vars.add("x1");
		vars.add("x2");
				
		mathML = "<apply><eq/><ci>x1</ci><ci>x2</ci></apply>";
		equal = new OntologyFunctionObject("omdoc://spsht-arith#equal", arguments, vars, "omdoc://MathML#Bool", mathML);
		
		// omdoc://spsht-arith#sum5
		arguments = new ArrayList<String>();
		arguments.add("omdoc://MathML#Real");
		arguments.add("omdoc://MathML#Real");
		arguments.add("omdoc://MathML#Real");
		arguments.add("omdoc://MathML#Real");
		arguments.add("omdoc://MathML#Real");
						
		vars = new ArrayList<String>();
		vars.add("x1");
		vars.add("x2");
		vars.add("x3");
		vars.add("x4");
		vars.add("x5");
						
		mathML = "<apply><plus/><ci>x1</ci><ci>x2</ci><ci>x3</ci><ci>x4</ci><ci>x5</ci></apply>";
		sum5 = new OntologyFunctionObject("omdoc://spsht-arith#sum5", arguments, vars, "omdoc://MathML#Real", mathML);
		
		// omdoc://winograd#revenue
		arguments = new ArrayList<String>();
		arguments.add("omdoc://winograd#Years");
								
		rev = new OntologyFunctionObject("omdoc://winograd#revenue", arguments, "omdoc://MathML#Real");
		
		// omdoc://winograd#expenses
		arguments = new ArrayList<String>();
		arguments.add("omdoc://winograd#Years");
		arguments.add("omdoc://winograd#Costs");
									
		expenses = new OntologyFunctionObject("omdoc://winograd#ExpensesPerYear", arguments, "omdoc://MathML#Real");
		
		// omdoc://winograd#domain
		arguments = new ArrayList<String>();
		arguments.add("omdoc://winograd#Years");

		vars = new ArrayList<String>();
		vars.add("x1");
		
								
		mathML = "<apply><csymbol cd=\"spsht-arith\">minus</csymbol><apply><csymbol cd=\"winograd\">ProfitPerYear</csymbol><ci>x1</ci></apply><apply><csymbol cd=\"winograd\">ExpensesPerYear</csymbol><ci>x1</ci><ci>Costtype: Total</ci></apply> </apply>";
		profit = new OntologyFunctionObject("omdoc://spsht-arith#profit", arguments, vars, "Real", mathML);
	}

	public OntologyFunctionObject getPlus() {
		return plus;
	}

	public OntologyFunctionObject getMinus() {
		return minus;
	}

	public OntologyFunctionObject getEqual() {
		return equal;
	}

	public OntologyFunctionObject getSum5() {
		return sum5;
	}

	public OntologyFunctionObject getRev() {
		return rev;
	}

	public OntologyFunctionObject getExpenses() {
		return expenses;
	}

	public OntologyFunctionObject getProfit() {
		return profit;
	}
	
	public List<OntologyFunctionObject> getAll() {
		List<OntologyFunctionObject> allObjs = new ArrayList<OntologyFunctionObject>();
		allObjs.add(getPlus());
		allObjs.add(getMinus());
		allObjs.add(getEqual());
		allObjs.add(getSum5());
		allObjs.add(getRev());
		allObjs.add(getExpenses());
		allObjs.add(getProfit());
		return allObjs;
	}
	
	
	

}
