package info.kwarc.sally.spreadsheet3.verification;

import info.kwarc.sally.spreadsheet3.Util;
import info.kwarc.sally.spreadsheet3.FormalSpreadsheet;
import info.kwarc.sally.spreadsheet3.model.Block;
import info.kwarc.sally.spreadsheet3.model.CellSpaceInformation;
import info.kwarc.sally.spreadsheet3.model.CellTuple;
import info.kwarc.sally.spreadsheet3.model.Manager;
import info.kwarc.sally.spreadsheet3.model.Relation;
import info.kwarc.sally.spreadsheet3.ontology.BuilderML;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class VerificationDataExtractor {
	
	static psf.ParserInterface parser = new psf.ParserInterface();
	//static String[] stdDataTypes = {"omdoc://MathML#Real", "omdoc://MathML#Int", "omdoc://MathML#Bool" };
	
	public static List<DataSymbolInformation> extractDataTypes(Map<Block, String> blocks, FormalSpreadsheet spreadsheet) {
		/*Map<String, List<String>> dataTypes = new HashMap<String,List<String>>();
		
		for (Block b : blocks.keySet()) {
			List<String> values;
			/*boolean isStdDT = false;
			for (String dt : stdDataTypes)
				if (dt.equals( blocks.get(b)) )
					isStdDT = true;* /
			
			if (dataTypes.containsKey(blocks.get(b)))
				values = dataTypes.get(blocks.get(b));
			else {
				values = new ArrayList<String>();
				dataTypes.put(blocks.get(b), values);
			}
			for (CellSpaceInformation pos : b.getCells()) {
				if ((spreadsheet.get(pos) != null) && 
						!spreadsheet.get(pos).getValue().isEmpty() &&
						!values.contains(b.getValueInterpretation( spreadsheet.get(pos).getValue()) ) )
					values.add(b.getValueInterpretation( spreadsheet.get(pos).getValue()) );
			}
		}*/
		
		List<DataSymbolInformation> dataObjects = new ArrayList<DataSymbolInformation>();
		
		for (Block b : blocks.keySet()) {
			for (CellSpaceInformation pos : b.getCells()) {
				if ((spreadsheet.get(pos) != null) && !spreadsheet.get(pos).getValue().isEmpty()) {
					dataObjects.add(new DataSymbolInformation(blocks.get(b), b.getValueInterpretation( spreadsheet.get(pos).getValue()), pos));
				}
			}
		}
		
		return dataObjects;
	}
	
	public static Map<Relation, String> extractCPSimilarFBs(Manager manager, FormalSpreadsheet spreadsheet, BuilderML builderML) {
		Map<Relation, String> mathMLRepresentations = new HashMap<Relation, String>();
		List<Relation> relations = manager.getAllRelations();
		for (Relation fbRelation : relations) {
			if (fbRelation.getRelationType().equals(Relation.RelationType.FUNCTIONALRELATION)) {
		
				Block fb = fbRelation.getBlocks().get(fbRelation.getBlocks().size()-1);
				boolean calculatedFb = true;
				for (int i = 0; i < fb.getCells().size(); i++) {
					if (spreadsheet.get(fb.getCells().get(i)).getFormula().isEmpty())
						calculatedFb = false;
				}
				if (calculatedFb) {
					List<String> formulae = new ArrayList<String>();
					List<List<String>> domainValues = new ArrayList<List<String>>();
					
					psf.SemanticMapping mapping = new psf.SemanticMapping();
					Map<CellSpaceInformation, String> interpretation = manager.getCompleteSemanticMapping(spreadsheet);
					for (CellSpaceInformation pos : interpretation.keySet()) 
						mapping.add(pos.getWorksheet(), pos.getRow(), pos.getColumn(), interpretation.get(pos));
					
					for (int i = 0; i < fb.getCells().size(); i++) {
						CellSpaceInformation pos = fb.getCells().get(i);
						psf.ParserParameter p = new psf.ParserParameter(spreadsheet.get(pos).getFormula(), pos.getWorksheet(), false, true, false, true, mapping.getMapping());
						formulae.add(parser.parseFormula(p).getMathML());
						
						List<String> dv = new ArrayList<String>();
						List<CellTuple> cellRelations = fbRelation.getCellRelationFor(pos);
						if (cellRelations.size() != 1)
							throw new java.lang.IllegalStateException("Number of cell relations for " + pos.toString() + " is not 1.");
						
						CellTuple cellTuple = cellRelations.get(0);
						List<Block> domain = fbRelation.getBlocks();
						domain.remove(domain.size()-1);
						for (int j = 0; j < domain.size(); j++) {
							dv.add(domain.get(j).getValueInterpretation(spreadsheet.get(cellTuple.getTuple().get(j)).getValue()));
						}
						domainValues.add(dv);
					}
					String antiunification = Util.antiunifyMathMLFormulae(formulae, domainValues, builderML);
					if (!antiunification.isEmpty()) {
						String equatation = builderML.getOperatorApplication("spsht-arith","equal") + "\n" 
								+ builderML.getOperatorApplication(Util.getCDFromURI(fbRelation.getUri()),
										                           Util.getSymbolFromURI(fbRelation.getUri())) + "\n";
						/*int variableCounter = 0;
						for (List<String> dv : domainValues)
							variableCounter = java.lang.Math.max(variableCounter, dv.size());
						for (int i = 0; i < variableCounter; i++)
							equatation = equatation + builderML.getIdentifier("?X" + i) + "\n";*/
						for (int i = 0; i < manager.getOntologyInterface().getFunctionObject(fbRelation.getUri()).getArgumentTypes().size(); i++ )
							equatation = equatation + builderML.getVIVaribale(i) + "\n";
						equatation = equatation + builderML.getApplicationEnd() + "\n" + Util.untagMathObject(antiunification, builderML) + builderML.getApplicationEnd() + "\n";
						mathMLRepresentations.put(fbRelation, equatation);
					}
				}
			}
		}
		return mathMLRepresentations;
	}
	
	public static Map<CellSpaceInformation, String> extractMLFormulaRepresentations(Relation fbRelation, Manager manager, FormalSpreadsheet spreadsheet, BuilderML builderML) {
		Map<CellSpaceInformation, String> mlFormulaeRep = new HashMap<CellSpaceInformation, String>();
		if (fbRelation.getRelationType().equals(Relation.RelationType.FUNCTIONALRELATION)) {
			Block fb = fbRelation.getBlocks().get(fbRelation.getBlocks().size()-1);
			
			psf.SemanticMapping mapping = new psf.SemanticMapping();
			Map<CellSpaceInformation, String> interpretation = manager.getCompleteSemanticMapping(spreadsheet);
			for (CellSpaceInformation pos : interpretation.keySet()) 
				mapping.add(pos.getWorksheet(), pos.getRow(), pos.getColumn(), interpretation.get(pos));
			
			for (CellSpaceInformation pos : fb.getCells()) {
				String cellFormula = spreadsheet.get(pos).getFormula();
				String mlFormulaRep = parser.parseFormula(new psf.ParserParameter(cellFormula, pos.getWorksheet(), false, true, false, true, mapping.getMapping())).getMathML();
				
				String equatation = builderML.getOperatorApplication("spsht-arith","equal") + "\n" 
						+ builderML.getOperatorApplication(Util.getCDFromURI(fbRelation.getUri()),
								                           Util.getSymbolFromURI(fbRelation.getUri())) + "\n";
				
				List<CellTuple> cellRelations = fbRelation.getCellRelationFor(pos);
				if (cellRelations.size() != 1)
					throw new java.lang.IllegalStateException("Number of cell relations for " + pos.toString() + " is not 1.");
				
				CellTuple cellTuple = cellRelations.get(0);
				List<Block> domain = fbRelation.getBlocks();
				domain.remove(domain.size()-1);
				for (int j = 0; j < domain.size(); j++) 
					equatation = equatation + domain.get(j).getValueInterpretation(spreadsheet.get(cellTuple.getTuple().get(j)).getValue()) + "\n";
			
				equatation = equatation + builderML.getApplicationEnd() + "\n" + Util.untagMathObject(mlFormulaRep, builderML) + builderML.getApplicationEnd() + "\n";
				mlFormulaeRep.put(pos, equatation);
			}
		}
		return mlFormulaeRep;
	}

}
