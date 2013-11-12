package info.kwarc.sally.spreadsheet3;

import info.kwarc.sally.spreadsheet3.ontology.AxiomObject;
import info.kwarc.sally.spreadsheet3.ontology.BuilderML;
import info.kwarc.sally.spreadsheet3.ontology.BuilderMathML;
import info.kwarc.sally.spreadsheet3.ontology.DataTypeObject;
import info.kwarc.sally.spreadsheet3.ontology.FunctionObject;
import info.kwarc.sally.spreadsheet3.ontology.IOntologyProvider;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class InterfaceMockup extends IOntologyProvider {
	Map<String, FunctionObject> ontologyBasicFunctions;
	Map<String, FunctionObject> ontologyDomainFunctions;
	Map<String, DataTypeObject> ontologyDataTypes;
	
	public InterfaceMockup() {
		super(new BuilderMathML());
		ontologyBasicFunctions = new HashMap<String, FunctionObject>();
		ontologyDomainFunctions = new HashMap<String, FunctionObject>();
		BuilderML mathMLBuilder = new BuilderMathML();
		
		// An ontology symbol is addressed by the identifier theoryname#symbolname
		
		// +++ Datatypes +++
		ontologyDataTypes = new HashMap<String, DataTypeObject>();
		ontologyDataTypes.put("spsht-numbers#spshReal", new DataTypeObject("spsht-numbers#spshReal", DataTypeObject.BasicType.Real));
		ontologyDataTypes.put("spsht-numbers#spshInt", new DataTypeObject("spsht-numbers#spshInt", DataTypeObject.BasicType.Int));
		ontologyDataTypes.put("spsht-bool#spshBool", new DataTypeObject("spsht-bool#spshBool", DataTypeObject.BasicType.Bool));
		ontologyDataTypes.put("spsht-strings#spshStrings", new DataTypeObject("spsht-strings#spshStrings", DataTypeObject.BasicType.String));
		ontologyDataTypes.put("timeinterval#yearAD", new DataTypeObject("timeinterval#yearAD", DataTypeObject.BasicType.String));
		ontologyDataTypes.put("money#monetary-quantity", new DataTypeObject("money#monetary-quantity", DataTypeObject.BasicType.Real));
		ontologyDataTypes.put("costs#cost", new DataTypeObject("costs#cost", DataTypeObject.BasicType.String));
		ontologyDataTypes.put("profits#profit", new DataTypeObject("profits#profit", DataTypeObject.BasicType.String));
		ontologyDataTypes.put("revenues#Revenues", new DataTypeObject("revenues#Revenues", DataTypeObject.BasicType.String));
		
		// +++ Functions +++
		
		// spsht-arith#plus
		List<String> arguments = new ArrayList<String>();
		arguments.add("spsht-numbers#spshReal");
		arguments.add("spsht-numbers#spshReal");
		
		String mathML = "<apply><plus/><rvar num=\"0\"/><rvar num=\"1\"/></apply>";
		ontologyBasicFunctions.put("spsht-arith#plus", new FunctionObject("spsht-arith#plus", arguments, "spsht-numbers#spshReal", mathML, mathMLBuilder));
	
		// spsht-arith#minus
		arguments = new ArrayList<String>();
		arguments.add("spsht-numbers#spshReal");
		arguments.add("spsht-numbers#spshReal");
		
		mathML = "<apply><minus/><rvar num=\"0\"/><rvar num=\"1\"/></apply>";
		ontologyBasicFunctions.put("spsht-arith#minus", new FunctionObject("spsht-arith#minus", arguments, "spsht-numbers#spshReal", mathML, mathMLBuilder));
		
		// spsht-arith#times
		arguments = new ArrayList<String>();
		arguments.add("spsht-numbers#spshReal");
		arguments.add("spsht-numbers#spshReal");
				
		mathML = "<apply><times/><rvar num=\"0\"/><rvar num=\"1\"/></apply>";
		ontologyBasicFunctions.put("spsht-arith#times", new FunctionObject("spsht-arith#times", arguments, "spsht-numbers#spshReal", mathML, mathMLBuilder));

		// spsht-arith#equal
		arguments = new ArrayList<String>();
		arguments.add("spsht-numbers#spshReal");
		arguments.add("spsht-numbers#spshReal");
			
		mathML = "<apply><eq/><rvar num=\"0\"/><rvar num=\"1\"/></apply>";
		ontologyBasicFunctions.put("spsht-arith#equal", new FunctionObject("spsht-arith#equal", arguments, "spsht-bool#spshBool", mathML, mathMLBuilder));
		
		// spsht-arith#sum5
		arguments = new ArrayList<String>();
		arguments.add("spsht-numbers#spshReal");
		arguments.add("spsht-numbers#spshReal");
		arguments.add("spsht-numbers#spshReal");
		arguments.add("spsht-numbers#spshReal");
		arguments.add("spsht-numbers#spshReal");
						
		mathML = "<apply><plus/><rvar num=\"0\"/><rvar num=\"1\"/><rvar num=\"2\"/><rvar num=\"3\"/><rvar num=\"4\"/></apply>";
		ontologyBasicFunctions.put("spsht-arith#sum5", new FunctionObject("spsht-arith#sum5", arguments, "spsht-numbers#spshReal", mathML, mathMLBuilder));
		
		// revenues#Revenues
		arguments = new ArrayList<String>();
		arguments.add("timeinterval#yearAD");
								
		ontologyDomainFunctions.put("revenues#RevenuesPerYear", new FunctionObject("revenues#RevenuesPerYear", arguments, "money#monetary-quantity"));
		
		// expenses#Expenses
		arguments = new ArrayList<String>();
		arguments.add("timeinterval#yearAD");
		arguments.add("costs#cost");
									
		ontologyDomainFunctions.put("expenses#ExpensesPerYear", new FunctionObject("expenses#ExpensesPerYear", arguments, "money#monetary-quantity"));
		
		// profitsd#profit
		arguments = new ArrayList<String>();
		arguments.add("timeinterval#yearAD");
							
		mathML = "<apply>\n" +
				 "  <csymbol cd=\"spsht-arith\">minus</csymbol>\n" +
				 "  <apply>\n" +
				 "    <csymbol cd=\"revenues\">RevenuesPerYear</csymbol>\n" +
				 "    <rvar num=\"0\"/>\n" +
				 "  </apply>\n" +
				 "  <apply>\n" +
				 "    <csymbol cd=\"expenses\">ExpensesPerYear</csymbol>\n" +
				 "    <rvar num=\"0\"/>\n" +
				 "    <ci>Total Costs</ci>\n" + 			// Value Interpretation. Correct approach ? 
				 "  </apply>\n" +
				 "</apply>\n";
		
		ontologyDomainFunctions.put("profits#ProfitPerYear", new FunctionObject("profits#ProfitPerYear", arguments, "money#monetary-quantity", mathML, mathMLBuilder));
	
	}
	
	@Override
	public FunctionObject getFunctionObject(String uri) {
		if (ontologyBasicFunctions.containsKey(uri))
			return ontologyBasicFunctions.get(uri);
		else
			return ontologyDomainFunctions.get(uri);
	}
	
	@Override
	public List<FunctionObject> getAllBasicFunctionObjects() {
		return new ArrayList<FunctionObject>(ontologyBasicFunctions.values());
	}
	
	@Override
	public Map<String, FunctionObject> getBasicFunctionObjectMap() {
		return new HashMap<String, FunctionObject>(ontologyBasicFunctions);
	}
	
	public List<FunctionObject> getAllDomainFunctionObjects() {
		return new ArrayList<FunctionObject>(ontologyDomainFunctions.values());
	}
	
	@Override
	public Map<String, FunctionObject> getDomainFunctionObjectMap() {
		return new HashMap<String, FunctionObject>(ontologyDomainFunctions);
	}
	
    @Override
    public DataTypeObject getDataTypeObject(String uri) {
    	return ontologyDataTypes.get(uri);
    	
    }
	
    @Override
	public List<DataTypeObject> getAllDataTypeObjects() {
    	return new ArrayList<DataTypeObject>(ontologyDataTypes.values());
    }
    
    @Override
    public Map<String, DataTypeObject> getDataTypeObjectMap() {
    	return new HashMap<String, DataTypeObject>(ontologyDataTypes);
    }
	
	@Override
	public List<AxiomObject> getAxioms() {
		List<AxiomObject> axioms = new ArrayList<AxiomObject>();
		axioms.add(getBuilderML().parseMLAxiom("<apply><forall/><bvar><ci>y</ci></bvar><condition><apply><in/><ci>y</ci><ci>timeinterval#yearAD</ci></apply></condition>" +
			"<apply><csymbol cd=\"spsht-arith\">equal</csymbol><apply><csymbol cd=\"expenses\">ExpensesPerYear</csymbol><ci>y</ci><ci>Total Costs</ci></apply>" +
			"<apply><csymbol cd=\"spsht-arith\">plus</csymbol>" +
			"<apply><csymbol cd=\"expenses\">ExpensesPerYear</csymbol><ci>y</ci><ci>Salary Costs</ci></apply>" +
			"<apply><csymbol cd=\"expenses\">ExpensesPerYear</csymbol><ci>y</ci><ci>Material Costs</ci></apply>" +
			"</apply></apply></apply>"));
		return axioms;
	}
	

}
