package info.kwarc.sally.spreadsheet3;

import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellDependencyDescription;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.ontology.BuilderML;
import info.kwarc.sally.spreadsheet3.ontology.ValueInterpretation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;


public class WinogradData {
	
	Manager manager;
	FormalSpreadsheet spreadsheet;
	Block year, cost, profit, dataInput, dataCalc, dataProfit; 
	Relation relationInput, relationCalc, relationProfit;
	
	public WinogradData() {
		
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
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",5,0), "Profit", "", ContentValueType.STRING_NUMBER);
		
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
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,1), "3.2", "B3+B4", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,2), "3.4", "C3+C4", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,3), "3.6", "D3+D4", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,4), "3.8", "E3+E4", ContentValueType.FLOAT);
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",5,1), "3.1", "B5-B2", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",5,2), "3.2", "C5-C2", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",5,3), "3.3", "D5-D2", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",5,4), "3.4", "E5-E2", ContentValueType.FLOAT);
		
		// Setting up the manager
		manager = new Manager(new InterfaceMockup());
		List<CellSpaceInformation> positionYear = Util.expandRange(
				new CellSpaceInformation("Table1",0,1), new CellSpaceInformation("Table1",0,4));
		year = manager.createComposedBlock(positionYear);
		
		List<CellSpaceInformation> positionCosts = Util.expandRange(
				new CellSpaceInformation("Table1",1,0), new CellSpaceInformation("Table1",4,0));
		cost = manager.createComposedBlock(positionCosts);
		
		List<CellSpaceInformation> positionDataInput = Util.expandRange(
				new CellSpaceInformation("Table1",1,1), new CellSpaceInformation("Table1",3,4));
		dataInput = manager.createComposedBlock(positionDataInput);
		
		List<CellSpaceInformation> positionDataCalc = Util.expandRange(
				new CellSpaceInformation("Table1",4,1), new CellSpaceInformation("Table1",4,4));
		dataCalc = manager.createComposedBlock(positionDataCalc);
		
		profit = manager.getOrCreateAtomicBlock(new CellSpaceInformation("Table1",5,0));
		
		List<CellSpaceInformation> positionDataProfit = Util.expandRange(
				new CellSpaceInformation("Table1",5,1), new CellSpaceInformation("Table1",5,4));
		dataProfit = manager.createComposedBlock(positionDataProfit);
		
		List<Block> blocksInput = new ArrayList<Block>();
		blocksInput.add(year);
		blocksInput.add(cost);
		blocksInput.add(dataInput);

		List<CellDependencyDescription> relationInputDesc = new ArrayList<CellDependencyDescription>();
		relationInputDesc.add(new CellDependencyDescription(0,2,0,3,"0,y;x,0;x,y"));
		relationInput = manager.createRelation(Relation.RelationType.FUNCTIONALRELATION, blocksInput, relationInputDesc);
 		
 		List<Block> blocksCalc = new ArrayList<Block>();
 		blocksCalc.add(year);
 		blocksCalc.add(cost);
 		blocksCalc.add(dataCalc);

 		List<CellDependencyDescription> relationCalcDesc = new ArrayList<CellDependencyDescription>();
		relationCalcDesc.add(new CellDependencyDescription(0,0,0,3,"0,y;x+3,0;x,y"));
 		relationCalc = manager.createRelation(Relation.RelationType.FUNCTIONALRELATION, blocksCalc, relationCalcDesc);
 		
 		List<Block> blocksProfit = new ArrayList<Block>();
 		blocksProfit.add(year);
 		blocksProfit.add(profit);
 		blocksProfit.add(dataProfit);

 		List<CellDependencyDescription> relationProfitDesc = new ArrayList<CellDependencyDescription>();
 		relationProfitDesc.add(new CellDependencyDescription(0,0,0,3,"0,y;x,0;x,y"));
 		relationProfit = manager.createRelation(Relation.RelationType.FUNCTIONALRELATION, blocksProfit, relationProfitDesc);
 		
 		// Setting up the ontology linking
 		BuilderML builderML = manager.getOntologyInterface().getBuilderML();
 		
 		Map<Integer, String> subExpressions = new HashMap<Integer,String>();
		subExpressions.put(new Integer(1), "\\d+");
		year.setValueInterpretation(new ValueInterpretation("#1", subExpressions, "<ci>Year <rvar num=\"1\"/> AD</ci>", builderML));
		
		Map<Integer, String> subExpressions2 = new HashMap<Integer,String>();
		subExpressions2.put(new Integer(1), "\\p{Alpha}+");
		cost.setValueInterpretation(new ValueInterpretation("#1", subExpressions2, "<ci>Costtype: <rvar num=\"1\"/></ci>", builderML));
		
		Map<Integer, String> subExpressions2a = new HashMap<Integer,String>();
		subExpressions2a.put(new Integer(1), "\\p{Alpha}+");
		profit.setValueInterpretation(new ValueInterpretation("#1", subExpressions2a, "<ci>Profit</ci>", builderML));
		
		Map<Integer, String> subExpressions3 = new HashMap<Integer,String>();
		subExpressions3.put(new Integer(1), "\\d+\\.\\d+");
		dataInput.setValueInterpretation(new ValueInterpretation("#1", subExpressions3, "<apply><csymbol cd=\"spsht-arith\">times</csymbol><ci>1000000</ci><ci><rvar num=\"1\"/></ci></apply>", builderML));
		
		Map<Integer, String> subExpressions4 = new HashMap<Integer,String>();
		subExpressions4.put(new Integer(1), "\\d+\\.\\d+");
		dataCalc.setValueInterpretation(new ValueInterpretation("#1", subExpressions4, "<apply><csymbol cd=\"spsht-arith\">times</csymbol><ci>1000000</ci><ci><rvar num=\"1\"/></ci></apply>", builderML));
		
		Map<Integer, String> subExpressions5 = new HashMap<Integer,String>();
		subExpressions5.put(new Integer(1), "\\d+\\.\\d+");
		dataProfit.setValueInterpretation(new ValueInterpretation("#1", subExpressions5, "<apply><csymbol cd=\"spsht-arith\">times</csymbol><ci>1000000</ci><ci><rvar num=\"1\"/></ci></apply>", builderML));
		
		relationInput.setUri("omdoc://winograd#ExpensesPerYear");
		relationCalc.setUri("omdoc://winograd#ExpensesPerYear");
		relationProfit.setUri("omdoc://winograd#profit");
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
	
	public Block getProfit() {
		return profit;
	}

	public Block getDataCalc() {
		return dataCalc;
	}

	public Block getDataInput() {
		return dataInput;
	}
	
	public Block getDataProfit() {
		return dataProfit;
	}

	public Relation getRelationInput() {
		return relationInput;
	}

	public Relation getRelationCalc() {
		return relationCalc;
	}

	public Relation getRelationProfit() {
		return relationProfit;
	}
	
}
