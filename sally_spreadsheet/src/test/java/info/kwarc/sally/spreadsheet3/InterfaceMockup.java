package info.kwarc.sally.spreadsheet3;

import info.kwarc.sally.spreadsheet3.ontology.AxiomObject;
import info.kwarc.sally.spreadsheet3.ontology.BuilderML;
import info.kwarc.sally.spreadsheet3.ontology.BuilderMathML;
import info.kwarc.sally.spreadsheet3.ontology.DataTypeObject;
import info.kwarc.sally.spreadsheet3.ontology.FunctionObject;
import info.kwarc.sally.spreadsheet3.ontology.IOntologyProvider;
import info.kwarc.sally.spreadsheet3.ontology.OntologyException;

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
		// http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?minus
		
		// +++ Datatypes +++
		ontologyDataTypes = new HashMap<String, DataTypeObject>();
		ontologyDataTypes.put("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal", new DataTypeObject("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal", DataTypeObject.BasicType.Real));
		ontologyDataTypes.put("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshInt", new DataTypeObject("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshInt", DataTypeObject.BasicType.Int));
		ontologyDataTypes.put("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/bool.omdoc?spsht-bool?spshBool", new DataTypeObject("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/bool.omdoc?spsht-bool?spshBool", DataTypeObject.BasicType.Bool));
		ontologyDataTypes.put("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/strings.omdoc?spsht-strings?strings", new DataTypeObject("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/strings.omdoc?spsht-strings?strings", DataTypeObject.BasicType.String));
		ontologyDataTypes.put("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/timeinterval.omdoc?timeinterval?yearAD", new DataTypeObject("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/timeinterval.omdoc?timeinterval?yearAD", DataTypeObject.BasicType.String));
		ontologyDataTypes.put("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/money.omdoc?money?monetary-quantity", new DataTypeObject("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/money.omdoc?money?monetary-quantity", DataTypeObject.BasicType.Real));
		ontologyDataTypes.put("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costs?sax-costs", new DataTypeObject("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costs?sax-costs", DataTypeObject.BasicType.String));
		ontologyDataTypes.put("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-profit.omdoc?sax-profit?sax-profit", new DataTypeObject("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-profit.omdoc?sax-profit?sax-profit", DataTypeObject.BasicType.String));
		ontologyDataTypes.put("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-revenues.omdoc?sax-revenues?sax-revenues", new DataTypeObject("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-revenues.omdoc?sax-revenues?sax-revenues", DataTypeObject.BasicType.String));
		
		// +++ Functions +++
		
		// spsht-arith#plus
		List<String> arguments = new ArrayList<String>();
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
		
		String mathML = "<apply><plus/><rvar num=\"0\"/><rvar num=\"1\"/></apply>";
		ontologyBasicFunctions.put("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?plus", new FunctionObject("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?plus", arguments, "http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal", mathML, mathMLBuilder));
	
		// spsht-arith#minus
		arguments = new ArrayList<String>();
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
		
		mathML = "<apply><minus/><rvar num=\"0\"/><rvar num=\"1\"/></apply>";
		ontologyBasicFunctions.put("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?minus", new FunctionObject("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?minus", arguments, "http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal", mathML, mathMLBuilder));
		
		// spsht-arith#times
		arguments = new ArrayList<String>();
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
				
		mathML = "<apply><times/><rvar num=\"0\"/><rvar num=\"1\"/></apply>";
		ontologyBasicFunctions.put("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?times", new FunctionObject("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?times", arguments, "http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal", mathML, mathMLBuilder));

		// spsht-arith#equal
		arguments = new ArrayList<String>();
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
			
		mathML = "<apply><eq/><rvar num=\"0\"/><rvar num=\"1\"/></apply>";
		ontologyBasicFunctions.put("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?equal", new FunctionObject("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?equal", arguments, "http://mathhub.info/KwarcMH/SiSsI/spshp/cds/bool.omdoc?spsht-bool?spshBool", mathML, mathMLBuilder));
		
		// spsht-arith#leq
		arguments = new ArrayList<String>();
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
			
		mathML = "<apply><leq/><rvar num=\"0\"/><rvar num=\"1\"/></apply>";
		ontologyBasicFunctions.put("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?lessEqual", new FunctionObject("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?lessEqual", arguments, "http://mathhub.info/KwarcMH/SiSsI/spshp/cds/bool.omdoc?spsht-bool?spshBool", mathML, mathMLBuilder));
		
		// spsht-arith#geq
		arguments = new ArrayList<String>();
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
			
		mathML = "<apply><geq/><rvar num=\"0\"/><rvar num=\"1\"/></apply>";
		ontologyBasicFunctions.put("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?greaterEqual", new FunctionObject("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?greaterEqual", arguments, "http://mathhub.info/KwarcMH/SiSsI/spshp/cds/bool.omdoc?spsht-bool?spshBool", mathML, mathMLBuilder));
		
		
		// spsht-arith#sum5
		arguments = new ArrayList<String>();
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal");
						
		mathML = "<apply><plus/><rvar num=\"0\"/><rvar num=\"1\"/><rvar num=\"2\"/><rvar num=\"3\"/><rvar num=\"4\"/></apply>";
		ontologyBasicFunctions.put("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?sum5", new FunctionObject("http://mathhub.info/KwarcMH/SiSsI/spshp/cds/arith.omdoc?spsht-arith?sum5", arguments, "http://mathhub.info/KwarcMH/SiSsI/spshp/cds/numbers.omdoc?spsht-numbers?spshReal", mathML, mathMLBuilder));
		
		// revenues#Revenues
		arguments = new ArrayList<String>();
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/timeinterval.omdoc?timeinterval?yearAD");
								
		ontologyDomainFunctions.put("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-revenues.omdoc?sax-revenues?sax-revenuesperti", new FunctionObject("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-revenues.omdoc?sax-revenues?sax-revenuesperti", arguments, "http://mathhub.info/KwarcMH/SiSsI/winograd/cds/money.omdoc?money?monetary-quantity"));
		
		// expenses#Expenses
		arguments = new ArrayList<String>();
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/timeinterval.omdoc?timeinterval?yearAD");
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costs?sax-costs");
									
		ontologyDomainFunctions.put("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costs?sax-costsperti", new FunctionObject("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costs?sax-costsperti", arguments, "http://mathhub.info/KwarcMH/SiSsI/winograd/cds/money.omdoc?money?monetary-quantity"));
		
		// profitsd#profit
		arguments = new ArrayList<String>();
		arguments.add("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/timeinterval.omdoc?timeinterval?yearAD");
							
		mathML = "<apply>\n" +
				 "  <csymbol cd=\"spsht-arith\">minus</csymbol>\n" +
				 "  <apply>\n" +
				 "    <csymbol cd=\"sax-revenues\">sax-revenuesperti</csymbol>\n" +
				 "    <rvar num=\"0\"/>\n" +
				 "  </apply>\n" +
				 "  <apply>\n" +
				 "    <csymbol cd=\"sax-costs\">sax-costsperti</csymbol>\n" +
				 "    <rvar num=\"0\"/>\n" +
				 "    <ci>Total Costs</ci>\n" + 			// Value Interpretation. Correct approach ? 
				 "  </apply>\n" +
				 "</apply>\n";
		
		ontologyDomainFunctions.put("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-profit.omdoc?sax-profit?sax-profitperti", new FunctionObject("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-profit.omdoc?sax-profit?sax-profitperti", arguments, "http://mathhub.info/KwarcMH/SiSsI/winograd/cds/money.omdoc?money?monetary-quantity", mathML, mathMLBuilder));
	
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
	public List<AxiomObject> getAxioms() throws OntologyException {
		List<AxiomObject> axioms = new ArrayList<AxiomObject>();
		axioms.add(getBuilderML().parseMLAxiom("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costs?sax-costs-Axiom1", "<apply><forall/><bvar><ci>y</ci></bvar><condition><apply><in/><ci>y</ci><ci>http://mathhub.info/KwarcMH/SiSsI/winograd/cds/timeinterval.omdoc?timeinterval?yearAD</ci></apply></condition>" +
			"<apply><csymbol cd=\"spsht-arith\">equal</csymbol><apply><csymbol cd=\"sax-costs\">sax-costsperti</csymbol><ci>y</ci><ci>Total Costs</ci></apply>" +
			"<apply><csymbol cd=\"spsht-arith\">plus</csymbol>" +
			"<apply><csymbol cd=\"sax-costs\">sax-costsperti</csymbol><ci>y</ci><ci>Salary Costs</ci></apply>" +
			"<apply><csymbol cd=\"sax-costs\">sax-costsperti</csymbol><ci>y</ci><ci>Material Costs</ci></apply>" +
			"</apply></apply></apply>"));
		axioms.add(getBuilderML().parseMLAxiom("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costs?sax-costs-Axiom2", "<apply><forall/><bvar><ci>c</ci></bvar><bvar><ci>y</ci></bvar><condition><apply><and/><apply><in/><ci>y</ci><ci>http://mathhub.info/KwarcMH/SiSsI/winograd/cds/timeinterval.omdoc?timeinterval?yearAD</ci></apply>"
				+ "<apply><in/><ci>c</ci><ci>http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costs?sax-costs</ci></apply></apply></condition>"
				+ "<apply><csymbol cd=\"spsht-arith\">lessEqual</csymbol>"
				+ "<apply><csymbol cd=\"sax-costs\">sax-costsperti</csymbol><ci>y</ci><ci>c</ci></apply>"
				+ "<apply><csymbol cd=\"sax-costs\">sax-costsperti</csymbol><ci>y</ci><ci>Total Costs</ci></apply>" 
				+ "</apply></apply>"));
		axioms.add(getBuilderML().parseMLAxiom("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/money.omdoc?money?monetary-quantity-Axiom1", "<apply><forall/><bvar><ci>c</ci></bvar><condition><apply><in/><ci>c</ci><ci>http://mathhub.info/KwarcMH/SiSsI/winograd/cds/money.omdoc?money?monetary-quantity</ci></apply></condition>"
				+ "<apply><csymbol cd=\"spsht-arith\">greaterEqual</csymbol>"
				+ "<ci>c</ci>"
				+ "<ci>100000</ci>" 
				+ "</apply></apply>"));
		return axioms;
	}
	
	

}
