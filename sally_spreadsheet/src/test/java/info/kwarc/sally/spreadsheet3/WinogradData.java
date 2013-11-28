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
	ConcreteSpreadsheet spreadsheet;
	Block year, revenues, cost, profit, dataRevenues, dataCosts, dataTotalCosts, dataProfit; 
	Relation relationRevenues, relationCosts, relationTotalCosts, relationProfit,
		typeYear, typeRevenues, typeCost, typeProfit, typeDataRevenues, typeDataCosts, typeDataTotalCosts, typeDataProfit;
	
	public WinogradData() {
		
		// +++ Setting up formal Spreadsheet +++
		spreadsheet = new ConcreteSpreadsheet();
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",0,1), "1984", "", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",0,2), "1985", "", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",0,3), "1986", "", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",0,4), "1987", "", ContentValueType.STRING_NUMBER);
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",1,0), "Revenues", "", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",2,0), "Material", "", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",3,0), "Salary","",  ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table1",4,0), "Total", "", ContentValueType.STRING_NUMBER);
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",5,0), "Profit", "", ContentValueType.STRING_NUMBER);
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",1,1), "4.1", "", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",1,2), "4.2", "", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",1,3), "4.3", "", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",1,4), "4.4", "", ContentValueType.FLOAT);
		
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
		
		spreadsheet.setContent(new CellSpaceInformation("Table1",5,1), "0.9", "B2-B5", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",5,2), "0.8", "C2-C5", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",5,3), "0.7", "D2-D5", ContentValueType.FLOAT);
		spreadsheet.setContent(new CellSpaceInformation("Table1",5,4), "0.6", "E2-E5", ContentValueType.FLOAT);
		
		// +++ Setting up the manager +++
		manager = new Manager(new InterfaceMockup());
		
		// +++ Setting up the ASM +++
		
		// Blocks
		List<CellSpaceInformation> positionYear = Util.expandRange(
				new CellSpaceInformation("Table1",0,1), new CellSpaceInformation("Table1",0,4));
		year = manager.createComposedBlock(positionYear);
		
		revenues = manager.getOrCreateAtomicBlock(new CellSpaceInformation("Table1",1,0));
		
		List<CellSpaceInformation> positionCosts = Util.expandRange(
				new CellSpaceInformation("Table1",2,0), new CellSpaceInformation("Table1",4,0));
		cost = manager.createComposedBlock(positionCosts);
		
		profit = manager.getOrCreateAtomicBlock(new CellSpaceInformation("Table1",5,0));
		
		
		List<CellSpaceInformation> positionDataRevenues = Util.expandRange(
				new CellSpaceInformation("Table1",1,1), new CellSpaceInformation("Table1",1,4));
		dataRevenues = manager.createComposedBlock(positionDataRevenues);
		
		List<CellSpaceInformation> positionDataCosts = Util.expandRange(
				new CellSpaceInformation("Table1",2,1), new CellSpaceInformation("Table1",3,4));
		dataCosts = manager.createComposedBlock(positionDataCosts);
		
		List<CellSpaceInformation> positionDataTotalCosts = Util.expandRange(
				new CellSpaceInformation("Table1",4,1), new CellSpaceInformation("Table1",4,4));
		dataTotalCosts = manager.createComposedBlock(positionDataTotalCosts);
		
		List<CellSpaceInformation> positionDataProfit = Util.expandRange(
				new CellSpaceInformation("Table1",5,1), new CellSpaceInformation("Table1",5,4));
		dataProfit = manager.createComposedBlock(positionDataProfit);
		
		// Functional relations
		List<Block> blocksRevenues = new ArrayList<Block>();
		blocksRevenues.add(year);
		//blocksRevenues.add(revenues);
		blocksRevenues.add(dataRevenues);

		List<CellDependencyDescription> relationRevenuesDesc = new ArrayList<CellDependencyDescription>();
		relationRevenuesDesc.add(new CellDependencyDescription(0,0,0,3,"0,y;x,y"));
		relationRevenues = manager.createRelation(Relation.RelationType.FUNCTIONALRELATION, blocksRevenues, relationRevenuesDesc);
		
		List<Block> blocksCosts = new ArrayList<Block>();
		blocksCosts.add(year);
		blocksCosts.add(cost);
		blocksCosts.add(dataCosts);

		List<CellDependencyDescription> relationCostsDesc = new ArrayList<CellDependencyDescription>();
		relationCostsDesc.add(new CellDependencyDescription(0,1,0,3,"0,y;x,0;x,y"));
		relationCosts = manager.createRelation(Relation.RelationType.FUNCTIONALRELATION, blocksCosts, relationCostsDesc);
 		
 		List<Block> blocksTotalCosts = new ArrayList<Block>();
 		blocksTotalCosts.add(year);
 		blocksTotalCosts.add(cost);
 		blocksTotalCosts.add(dataTotalCosts);

 		List<CellDependencyDescription> relationTotalCostsDesc = new ArrayList<CellDependencyDescription>();
		relationTotalCostsDesc.add(new CellDependencyDescription(0,0,0,3,"0,y;x+2,0;x,y"));
 		relationTotalCosts = manager.createRelation(Relation.RelationType.FUNCTIONALRELATION, blocksTotalCosts, relationTotalCostsDesc);
 		
 		List<Block> blocksProfit = new ArrayList<Block>();
 		blocksProfit.add(year);
 		//blocksProfit.add(profit);
 		blocksProfit.add(dataProfit);

 		List<CellDependencyDescription> relationProfitDesc = new ArrayList<CellDependencyDescription>();
 		relationProfitDesc.add(new CellDependencyDescription(0,0,0,3,"0,y;x,y"));
 		relationProfit = manager.createRelation(Relation.RelationType.FUNCTIONALRELATION, blocksProfit, relationProfitDesc);
 		
 		// Type relations
 		typeYear = manager.createUnaryRelation(Relation.RelationType.TYPERELATION, year);
 		typeRevenues = manager.createUnaryRelation(Relation.RelationType.TYPERELATION, revenues);
 		typeCost = manager.createUnaryRelation(Relation.RelationType.TYPERELATION, cost);
 		typeProfit = manager.createUnaryRelation(Relation.RelationType.TYPERELATION, profit);
 		typeDataRevenues = manager.createUnaryRelation(Relation.RelationType.TYPERELATION, dataRevenues);
 		typeDataCosts = manager.createUnaryRelation(Relation.RelationType.TYPERELATION, dataCosts);
 		typeDataTotalCosts = manager.createUnaryRelation(Relation.RelationType.TYPERELATION, dataTotalCosts);
 		typeDataProfit = manager.createUnaryRelation(Relation.RelationType.TYPERELATION, dataProfit);
 		
 		// +++ Setting up the ontology linking +++
 		
 		// Value Interpretation
 		BuilderML builderML = manager.getOntologyInterface().getBuilderML();
 		
 		Map<Integer, String> subExpressions = new HashMap<Integer,String>();
		subExpressions.put(new Integer(1), "\\d+");
		year.setValueInterpretation(new ValueInterpretation("#1", subExpressions, "<ci>Year <rvar num=\"1\"/> AD</ci>", builderML));
		
		Map<Integer, String> subExpressions1a = new HashMap<Integer,String>();
		subExpressions1a.put(new Integer(1), "\\p{Alpha}+");
		revenues.setValueInterpretation(new ValueInterpretation("#1", subExpressions1a, "<ci>Revenues</ci>", builderML));
		
		Map<Integer, String> subExpressions2 = new HashMap<Integer,String>();
		subExpressions2.put(new Integer(1), "\\p{Alpha}+");
		cost.setValueInterpretation(new ValueInterpretation("#1", subExpressions2, "<ci><rvar num=\"1\"/> Costs</ci>", builderML));
		
		Map<Integer, String> subExpressions2a = new HashMap<Integer,String>();
		subExpressions2a.put(new Integer(1), "\\p{Alpha}+");
		profit.setValueInterpretation(new ValueInterpretation("#1", subExpressions2a, "<ci>Profit</ci>", builderML));
		
		Map<Integer, String> subExpressions3a = new HashMap<Integer,String>();
		subExpressions3a.put(new Integer(1), "\\d+\\.\\d+");
		dataRevenues.setValueInterpretation(new ValueInterpretation("#1", subExpressions3a, "<apply><csymbol cd=\"spsht-arith\">times</csymbol><ci>1000000</ci><ci><rvar num=\"1\"/></ci></apply>", builderML));
		
		Map<Integer, String> subExpressions3 = new HashMap<Integer,String>();
		subExpressions3.put(new Integer(1), "\\d+\\.\\d+");
		dataCosts.setValueInterpretation(new ValueInterpretation("#1", subExpressions3, "<apply><csymbol cd=\"spsht-arith\">times</csymbol><ci>1000000</ci><ci><rvar num=\"1\"/></ci></apply>", builderML));
		
		Map<Integer, String> subExpressions4 = new HashMap<Integer,String>();
		subExpressions4.put(new Integer(1), "\\d+\\.\\d+");
		dataTotalCosts.setValueInterpretation(new ValueInterpretation("#1", subExpressions4, "<apply><csymbol cd=\"spsht-arith\">times</csymbol><ci>1000000</ci><ci><rvar num=\"1\"/></ci></apply>", builderML));
		
		Map<Integer, String> subExpressions5 = new HashMap<Integer,String>();
		subExpressions5.put(new Integer(1), "\\d+\\.\\d+");
		dataProfit.setValueInterpretation(new ValueInterpretation("#1", subExpressions5, "<apply><csymbol cd=\"spsht-arith\">times</csymbol><ci>1000000</ci><ci><rvar num=\"1\"/></ci></apply>", builderML));
		
		// Relation linking
		relationRevenues.setUri("revenues#RevenuesPerYear");
		relationCosts.setUri("expenses#ExpensesPerYear");
		relationTotalCosts.setUri("expenses#ExpensesPerYear");
		relationProfit.setUri("profits#ProfitPerYear");
		
		typeYear.setUri("timeinterval#yearAD");
		typeRevenues.setUri("revenues#Revenues");
		typeCost.setUri("costs#cost");
		typeProfit.setUri("profits#profit");
		typeDataRevenues.setUri("money#monetary-quantity");
		typeDataCosts.setUri("money#monetary-quantity");
		typeDataTotalCosts.setUri("money#monetary-quantity");
		typeDataProfit.setUri("money#monetary-quantity");
	}

	public Manager getManager() {
		return manager;
	}

	public ConcreteSpreadsheet getSpreadsheet() {
		return spreadsheet;
	}

	public Block getYear() {
		return year;
	}
	
	public Block getRevenues() {
		return revenues;
	}

	public Block getCost() {
		return cost;
	}
	
	public Block getProfit() {
		return profit;
	}
	
	public Block getDataRevenues() {
		return dataRevenues;
	}
	
	public Block getDataCosts() {
		return dataCosts;
	}

	public Block getDataTotalCosts() {
		return dataTotalCosts;
	}
	
	public Block getDataProfit() {
		return dataProfit;
	}
	
	public Relation getRelationRevenues() {
		return relationRevenues;
	}

	public Relation getRelationCosts() {
		return relationCosts;
	}

	public Relation getRelationTotalCosts() {
		return relationTotalCosts;
	}

	public Relation getRelationProfit() {
		return relationProfit;
	}

	public Relation getTypeYear() {
		return typeYear;
	}
	
	public Relation getTypeRevenues() {
		return typeRevenues;
	}

	public Relation getTypeCost() {
		return typeCost;
	}

	public Relation getTypeProfit() {
		return typeProfit;
	}
	
	public Relation getTypeDataRevenues() {
		return typeDataRevenues;
	}

	public Relation getTypeDataCosts() {
		return typeDataCosts;
	}

	public Relation getTypeDataTotalCosts() {
		return typeDataTotalCosts;
	}

	public Relation getTypeDataProfit() {
		return typeDataProfit;
	}
	
}
