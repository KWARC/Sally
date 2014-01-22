package info.kwarc.sally.spreadsheet3;

import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellDependencyDescription;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.ModelException;
import info.kwarc.sally.spreadsheet3.model.ModelManager;
import info.kwarc.sally.spreadsheet3.model.PropertyName;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.model.RelationOntologyLink;
import info.kwarc.sally.spreadsheet3.ontology.BuilderML;
import info.kwarc.sally.spreadsheet3.ontology.ValueInterpretation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;


public class WinogradData {
	
	Manager manager;
	ModelManager modelManager;
	ConcreteSpreadsheet spreadsheet;
	Block year, year2, revenues, cost, profit, dataRevenues, dataCosts, dataTotalCosts, dataProfit; 
	Relation relationRevenues, relationCosts, relationTotalCosts, relationTotalCosts2, relationProfit,
		typeYear, typeYear2, typeRevenues, typeCost, typeProfit, typeDataRevenues, typeDataCosts, typeDataTotalCosts, typeDataProfit;
	
	public WinogradData() throws ModelException {
		manager = new Manager(new InterfaceMockup());
		
		// +++ Setting up formal Spreadsheet +++
		spreadsheet = manager.getSpreadsheet();
		
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
		modelManager = manager.getModel();
		
		// +++ Setting up the ASM +++
		
		// Blocks
		List<CellSpaceInformation> positionYear = Util.expandRange(
				new CellSpaceInformation("Table1",0,1), new CellSpaceInformation("Table1",0,4));
		year = modelManager.createComposedBlock(positionYear);
		year.setProperty(PropertyName.COMPLETESEMANTICBLOCK, "true");
		
		revenues = modelManager.getOrCreateAtomicBlock(new CellSpaceInformation("Table1",1,0));
		revenues.setProperty(PropertyName.COMPLETESEMANTICBLOCK, "true");
		
		List<CellSpaceInformation> positionCosts = Util.expandRange(
				new CellSpaceInformation("Table1",2,0), new CellSpaceInformation("Table1",4,0));
		cost = modelManager.createComposedBlock(positionCosts);
		cost.setProperty(PropertyName.COMPLETESEMANTICBLOCK, "true");
		
		profit = modelManager.getOrCreateAtomicBlock(new CellSpaceInformation("Table1",5,0));
		profit.setProperty(PropertyName.COMPLETESEMANTICBLOCK, "true");
		
		List<CellSpaceInformation> positionDataRevenues = Util.expandRange(
				new CellSpaceInformation("Table1",1,1), new CellSpaceInformation("Table1",1,4));
		dataRevenues = modelManager.createComposedBlock(positionDataRevenues);
		
		List<CellSpaceInformation> positionDataCosts = Util.expandRange(
				new CellSpaceInformation("Table1",2,1), new CellSpaceInformation("Table1",3,4));
		dataCosts = modelManager.createComposedBlock(positionDataCosts);
		
		List<CellSpaceInformation> positionDataTotalCosts = Util.expandRange(
				new CellSpaceInformation("Table1",4,1), new CellSpaceInformation("Table1",4,4));
		dataTotalCosts = modelManager.createComposedBlock(positionDataTotalCosts);
		
		List<CellSpaceInformation> positionDataProfit = Util.expandRange(
				new CellSpaceInformation("Table1",5,1), new CellSpaceInformation("Table1",5,4));
		dataProfit = modelManager.createComposedBlock(positionDataProfit);
		
		// Functional relations
		List<Block> blocksRevenues = new ArrayList<Block>();
		blocksRevenues.add(year);
		//blocksRevenues.add(revenues);
		blocksRevenues.add(dataRevenues);

		List<CellDependencyDescription> relationRevenuesDesc = new ArrayList<CellDependencyDescription>();
		relationRevenuesDesc.add(new CellDependencyDescription(0,0,0,3,"0,y;x,y"));
		relationRevenues = modelManager.createRelation(Relation.RelationType.FUNCTIONALRELATION, blocksRevenues, relationRevenuesDesc);
		
		List<Block> blocksCosts = new ArrayList<Block>();
		blocksCosts.add(year);
		blocksCosts.add(cost);
		blocksCosts.add(dataCosts);

		List<CellDependencyDescription> relationCostsDesc = new ArrayList<CellDependencyDescription>();
		relationCostsDesc.add(new CellDependencyDescription(0,1,0,3,"0,y;x,0;x,y"));
		relationCosts = modelManager.createRelation(Relation.RelationType.FUNCTIONALRELATION, blocksCosts, relationCostsDesc);
 		
 		List<Block> blocksTotalCosts = new ArrayList<Block>();
 		blocksTotalCosts.add(year);
 		blocksTotalCosts.add(cost);
 		blocksTotalCosts.add(dataTotalCosts);

 		List<CellDependencyDescription> relationTotalCostsDesc = new ArrayList<CellDependencyDescription>();
		relationTotalCostsDesc.add(new CellDependencyDescription(0,0,0,3,"0,y;x+2,0;x,y"));
 		relationTotalCosts = modelManager.createRelation(Relation.RelationType.FUNCTIONALRELATION, blocksTotalCosts, relationTotalCostsDesc);
 		
 		List<Block> blocksProfit = new ArrayList<Block>();
 		blocksProfit.add(year);
 		//blocksProfit.add(profit);
 		blocksProfit.add(dataProfit);

 		List<CellDependencyDescription> relationProfitDesc = new ArrayList<CellDependencyDescription>();
 		relationProfitDesc.add(new CellDependencyDescription(0,0,0,3,"0,y;x,y"));
 		relationProfit = modelManager.createRelation(Relation.RelationType.FUNCTIONALRELATION, blocksProfit, relationProfitDesc);
 		
 		// Type relations
 		typeYear = modelManager.createUnaryRelation(Relation.RelationType.TYPERELATION, year);
 		typeRevenues = modelManager.createUnaryRelation(Relation.RelationType.TYPERELATION, revenues);
 		typeCost = modelManager.createUnaryRelation(Relation.RelationType.TYPERELATION, cost);
 		typeProfit = modelManager.createUnaryRelation(Relation.RelationType.TYPERELATION, profit);
 		typeDataRevenues = modelManager.createUnaryRelation(Relation.RelationType.TYPERELATION, dataRevenues);
 		typeDataCosts = modelManager.createUnaryRelation(Relation.RelationType.TYPERELATION, dataCosts);
 		typeDataTotalCosts = modelManager.createUnaryRelation(Relation.RelationType.TYPERELATION, dataTotalCosts);
 		typeDataProfit = modelManager.createUnaryRelation(Relation.RelationType.TYPERELATION, dataProfit);
 		
 		// +++ Setting up the ontology linking +++
 		
 		// Value Interpretation
 		BuilderML builderML = manager.getOntology().getBuilderML();
 		
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
		relationRevenues.setUri("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-revenues.omdoc?sax-revenues?sax-revenuesperti");
		relationCosts.setUri("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costs?sax-costsperti");
		relationTotalCosts.setUri("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costs?sax-costsperti");
		relationProfit.setUri("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-profit.omdoc?sax-profit?sax-profitperti");
		
		typeYear.setUri("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/timeinterval.omdoc?timeinterval?yearAD");
		typeRevenues.setUri("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-revenues.omdoc?sax-revenues?sax-revenues");
		typeCost.setUri("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costs?sax-costs");
		typeProfit.setUri("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-profit.omdoc?sax-profit?sax-profit");
		typeDataRevenues.setUri("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/money.omdoc?money?monetary-quantity");
		typeDataCosts.setUri("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/money.omdoc?money?monetary-quantity");
		typeDataTotalCosts.setUri("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/money.omdoc?money?monetary-quantity");
		typeDataProfit.setUri("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/money.omdoc?money?monetary-quantity");
	}
	
	public void createSecondWorksheet() {
		spreadsheet.setContent(new CellSpaceInformation("Table2",0,1), "1984", "", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table2",0,2), "1985", "", ContentValueType.STRING_NUMBER);
		spreadsheet.setContent(new CellSpaceInformation("Table2",0,3), "1986", "", ContentValueType.STRING_NUMBER);
		
		List<CellSpaceInformation> positionYear = Util.expandRange(
				new CellSpaceInformation("Table2",0,1), new CellSpaceInformation("Table2",0,3));
		year2 = modelManager.createComposedBlock(positionYear);
		year2.setProperty(PropertyName.COMPLETESEMANTICBLOCK, "true");
		
		typeYear2 = modelManager.createUnaryRelation(Relation.RelationType.TYPERELATION, year2);
		
		BuilderML builderML = manager.getOntology().getBuilderML();
 		
 		Map<Integer, String> subExpressions = new HashMap<Integer,String>();
		subExpressions.put(new Integer(1), "\\d+");
		year2.setValueInterpretation(new ValueInterpretation("#1", subExpressions, "<ci>Year <rvar num=\"1\"/> AD</ci>", builderML));
		
		typeYear2.setUri("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/timeinterval.omdoc?timeinterval?yearAD");
	}
	
	public void createSecondeTCRelation() throws ModelException {
		List<Block> blocksTotalCosts = new ArrayList<Block>();
 		blocksTotalCosts.add(year);
 		blocksTotalCosts.add(dataTotalCosts);

 		List<CellDependencyDescription> relationTotalCostsDesc = new ArrayList<CellDependencyDescription>();
		relationTotalCostsDesc.add(new CellDependencyDescription(0,0,0,3,"0,y;x,y"));
 		relationTotalCosts2 = modelManager.createRelation(Relation.RelationType.FUNCTIONALRELATION, blocksTotalCosts, relationTotalCostsDesc);
 		
 		List<String> parameterLink = new ArrayList<String>();
 		parameterLink.add("0");
 		parameterLink.add("<ci>Total Costs</ci>");
 		
 		relationTotalCosts2.setOntologyLink(new RelationOntologyLink("http://mathhub.info/KwarcMH/SiSsI/winograd/cds/sax-costs.omdoc?sax-costs?sax-costsperti", parameterLink));
	}
	
	public Manager getManager() {
		return manager;
	}

	public ModelManager getModelManager() {
		return modelManager;
	}

	public ConcreteSpreadsheet getSpreadsheet() {
		return spreadsheet;
	}

	public Block getYear() {
		return year;
	}
	
	public Block getYear2() {
		return year2;
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
	
	public Relation getRelationTotalCosts2() {
		return relationTotalCosts2;
	}

	public Relation getRelationProfit() {
		return relationProfit;
	}

	public Relation getTypeYear() {
		return typeYear;
	}
	
	public Relation getTypeYear2() {
		return typeYear2;
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
