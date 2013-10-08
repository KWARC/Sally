package info.kwarc.sally.spreadsheet2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;


public class WinogradData {
	
	Manager manager;
	FormalSpreadsheet spreadsheet;
	Block year, cost, dataInput, dataCalc;
	Relation relationInput, relationCalc;
	BuilderML builderML;
	
	public WinogradData() {
		builderML = new BuilderMathML();
		
		// Setting up formal Spreadsheet
		spreadsheet = new FormalSpreadsheet();
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",0,1), "1984", "", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",0,2), "1985", "", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",0,3), "1986", "", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",0,4), "1987", "", ContentValueType.STRING_NUMBER);
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",1,0), "Revenues", "", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",2,0), "Materials", "", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",3,0), "Salaries","",  ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,0), "total", "", ContentValueType.STRING_NUMBER);
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",1,1), "0.1", "", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",1,2), "0.2", "", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",1,3), "0.3", "", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",1,4), "0.4", "", ContentValueType.FLOAT);
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",2,1), "1.1", "", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",2,2), "1.2", "", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",2,3), "1.3", "", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",2,4), "1.4", "", ContentValueType.FLOAT);
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",3,1), "2.1", "", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",3,2), "2.2", "", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",3,3), "2.3", "", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",3,4), "2.4", "", ContentValueType.FLOAT);
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,1), "3.2", "B2+B3", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,2), "3.4", "C2+C3", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,3), "3.6", "D2+D3", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,4), "3.8", "E2+E3", ContentValueType.FLOAT);
		
		// Setting up the manager
		manager = new Manager();
		List<CellSpaceInformation> positionYear = Util.expandRange(
				new CellSpaceInformation("Table1",0,1), new CellSpaceInformation("Table1",0,4));
		year = manager.createComposedBlock(positionYear);;
		
		List<CellSpaceInformation> positionCosts = Util.expandRange(
				new CellSpaceInformation("Table1",1,0), new CellSpaceInformation("Table1",4,0));
		cost = manager.createComposedBlock(positionCosts);
		
		List<CellSpaceInformation> positionDataInput = Util.expandRange(
				new CellSpaceInformation("Table1",1,1), new CellSpaceInformation("Table1",3,4));
		dataInput = manager.createComposedBlock(positionDataInput);
		
		List<CellSpaceInformation> positionDataCalc = Util.expandRange(
				new CellSpaceInformation("Table1",4,1), new CellSpaceInformation("Table1",4,4));
		dataCalc = manager.createComposedBlock(positionDataCalc);
		
		List<Block> blocksInput = new ArrayList<Block>();
		blocksInput.add(year);
		blocksInput.add(cost);
		blocksInput.add(dataInput);

 		relationInput = manager.createFunctionalRelation(blocksInput);
 		
 		List<Block> blocksCalc = new ArrayList<Block>();
 		blocksCalc.add(year);
 		blocksCalc.add(cost);
 		blocksCalc.add(dataCalc);

 		relationCalc = manager.createFunctionalRelation(blocksCalc);
 		
 		// Setting up the ontology linking
 		Map<Integer, String> subExpressions = new HashMap<Integer,String>();
		subExpressions.put(new Integer(1), "\\d+");
		ValueInterpretation vi = new ValueInterpretation("#1", subExpressions, "<ci>Year <rvar num=\"1\"/> AD</ci>", builderML);
		year.setOntologyLink(new OntologyBlockLink("omdoc://winograd#Years", vi));
		
		Map<Integer, String> subExpressions2 = new HashMap<Integer,String>();
		subExpressions2.put(new Integer(1), "\\p{Alpha}+");
		ValueInterpretation vi2 = new ValueInterpretation("#1", subExpressions2, "<ci>Costtype: <rvar num=\"1\"/></ci>", builderML);
		cost.setOntologyLink(new OntologyBlockLink("omdoc://winograd#Costs", vi2));
		
		Map<Integer, String> subExpressions3 = new HashMap<Integer,String>();
		subExpressions3.put(new Integer(1), "\\d+\\.\\d+");
		ValueInterpretation vi3 = new ValueInterpretation("#1", subExpressions3, "<apply><csymbol cd=\"spsht-arith\">times</csymbol><ci>1000000</ci><ci><rvar num=\"1\"/></ci></apply>", builderML);
		dataInput.setOntologyLink(new OntologyBlockLink("omdoc://MathML#Real", vi3));
		
		blocksInput.remove(blocksInput.size()-1);
		relationInput.setOntologyLink( new OntologyRelationLink("omdoc://winograd#ExpensesPerYear",
				"<apply><csymbol cd=\"LocalDomain\">Expenses per Year</csymbol><rvar num=\"1\"/><rvar num=\"2\"/></apply>", Util.convertBlocksToOntologyLinks(blocksInput),builderML));
		
		Map<Integer, String> subExpressions4 = new HashMap<Integer,String>();
		subExpressions4.put(new Integer(1), "\\d+\\.\\d+");
		ValueInterpretation vi4 = new ValueInterpretation("#1", subExpressions4, "<apply><csymbol cd=\"spsht-arith\">times</csymbol><ci>1000000</ci><ci><rvar num=\"1\"/></ci></apply>", builderML);
		dataCalc.setOntologyLink(new OntologyBlockLink("omdoc://MathML#Real", vi4));
		
		blocksCalc.remove(blocksCalc.size()-1);
		relationCalc.setOntologyLink( new OntologyRelationLink("omdoc://winograd#ExpensesPerYear",
				"<apply><csymbol cd=\"LocalDomain\">Expenses per Year</csymbol><rvar num=\"1\"/><rvar num=\"2\"/></apply>", Util.convertBlocksToOntologyLinks(blocksCalc),builderML));
	}

	public Manager getManager() {
		return manager;
	}

	public FormalSpreadsheet getSpreadsheet() {
		return spreadsheet;
	}

	public Block getYear() {
		return year;
	}

	public Block getCost() {
		return cost;
	}

	public Block getDataCalc() {
		return dataCalc;
	}

	public Block getDataInput() {
		return dataInput;
	}

	public Relation getRelationInput() {
		return relationInput;
	}

	public Relation getRelationCalc() {
		return relationCalc;
	}

	
}
