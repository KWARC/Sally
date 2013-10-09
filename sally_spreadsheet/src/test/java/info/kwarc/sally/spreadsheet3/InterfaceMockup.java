package info.kwarc.sally.spreadsheet3;

import info.kwarc.sally.spreadsheet3.ontology.BuilderML;
import info.kwarc.sally.spreadsheet3.ontology.BuilderMathML;
import info.kwarc.sally.spreadsheet3.ontology.FunctionObject;
import info.kwarc.sally.spreadsheet3.ontology.Interface;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class InterfaceMockup extends Interface {
	Map<String, FunctionObject> ontologyFunctions;
	
	public InterfaceMockup() {
		super(new BuilderMathML());
		ontologyFunctions = new HashMap<String, FunctionObject>();
		BuilderML mathMLBuilder = new BuilderMathML();
		
		// omdoc://spsht-arith#plus
		List<String> arguments = new ArrayList<String>();
		arguments.add("omdoc://MathML#Real");
		arguments.add("omdoc://MathML#Real");
		
		/*List<String> vars = new ArrayList<String>();
		vars.add("<rvar num=\"1\"/>");
		vars.add("<rvar num=\"2\"/>");*/
		
		String mathML = "<apply><plus/><rvar num=\"1\"/><rvar num=\"2\"/></apply>";
		ontologyFunctions.put("omdoc://spsht-arith#plus", new FunctionObject("omdoc://spsht-arith#plus", arguments, "omdoc://MathML#Real", mathML, mathMLBuilder));
	
		// omdoc://spsht-arith#minus
		arguments = new ArrayList<String>();
		arguments.add("omdoc://MathML#Real");
		arguments.add("omdoc://MathML#Real");
				
		/*vars = new ArrayList<String>();
		vars.add("<rvar num=\"1\"/>");
		vars.add("<rvar num=\"2\"/>");*/
				
		mathML = "<apply><minus/><rvar num=\"1\"/><rvar num=\"2\"/></apply>";
		ontologyFunctions.put("omdoc://spsht-arith#minus", new FunctionObject("omdoc://spsht-arith#minus", arguments, "omdoc://MathML#Real", mathML, mathMLBuilder));
		
		// omdoc://spsht-arith#equal
		arguments = new ArrayList<String>();
		arguments.add("omdoc://MathML#Real");
		arguments.add("omdoc://MathML#Real");
				
		/*vars = new ArrayList<String>();
		vars.add("<rvar num=\"1\"/>");
		vars.add("<rvar num=\"2\"/>");*/
				
		mathML = "<apply><eq/><rvar num=\"1\"/><rvar num=\"2\"/></apply>";
		ontologyFunctions.put("omdoc://spsht-arith#equal", new FunctionObject("omdoc://spsht-arith#equal", arguments, "omdoc://MathML#Bool", mathML, mathMLBuilder));
		
		// omdoc://spsht-arith#sum5
		arguments = new ArrayList<String>();
		arguments.add("omdoc://MathML#Real");
		arguments.add("omdoc://MathML#Real");
		arguments.add("omdoc://MathML#Real");
		arguments.add("omdoc://MathML#Real");
		arguments.add("omdoc://MathML#Real");
						
		/*vars = new ArrayList<String>();
		vars.add("<rvar num=\"1\"/>");
		vars.add("<rvar num=\"2\"/>");
		vars.add("<rvar num=\"3\"/>");
		vars.add("<rvar num=\"4\"/>");
		vars.add("<rvar num=\"5\"/>");*/
						
		mathML = "<apply><plus/><rvar num=\"1\"/><rvar num=\"2\"/><rvar num=\"3\"/><rvar num=\"4\"/><rvar num=\"5\"/></apply>";
		ontologyFunctions.put("omdoc://spsht-arith#sum5", new FunctionObject("omdoc://spsht-arith#sum5", arguments, "omdoc://MathML#Real", mathML, mathMLBuilder));
		
		// omdoc://winograd#revenue
		arguments = new ArrayList<String>();
		arguments.add("omdoc://winograd#Years");
								
		ontologyFunctions.put("omdoc://winograd#RevenuePerYear", new FunctionObject("omdoc://winograd#RevenuePerYear", arguments, "omdoc://MathML#Real"));
		
		// omdoc://winograd#expenses
		arguments = new ArrayList<String>();
		arguments.add("omdoc://winograd#Years");
		arguments.add("omdoc://winograd#Costs");
									
		ontologyFunctions.put("omdoc://winograd#ExpensesPerYear", new FunctionObject("omdoc://winograd#ExpensesPerYear", arguments, "omdoc://MathML#Real"));
		
		// omdoc://winograd#profit
		arguments = new ArrayList<String>();
		arguments.add("omdoc://winograd#Years");

		/*vars = new ArrayList<String>();
		vars.add("<rvar num=\"1\"/>");*/
							
		mathML = "<apply>\n" +
				 "  <csymbol cd=\"spsht-arith\">minus</csymbol>\n" +
				 "  <apply>\n" +
				 "    <csymbol cd=\"winograd\">RevenuePerYear</csymbol>\n" +
				 "    <rvar num=\"1\"/>\n" +
				 "  </apply>\n" +
				 "  <apply>\n" +
				 "    <csymbol cd=\"winograd\">ExpensesPerYear</csymbol>\n" +
				 "    <rvar num=\"1\"/>\n" +
				 "    <ci>Costtype: Total</ci>\n" +
				 "  </apply>\n" +
				 "</apply>\n";
		ontologyFunctions.put("omdoc://winograd#profit", new FunctionObject("omdoc://spsht-arith#profit", arguments, "Real", mathML, mathMLBuilder));
		
	}
	
	@Override
	public FunctionObject getFunctionObject(String uri) {
		return ontologyFunctions.get(uri);
	}
	
	@Override
	public List<FunctionObject> getAllFunctionObjects() {
		return new ArrayList<FunctionObject>(ontologyFunctions.values());
	}
	

}
